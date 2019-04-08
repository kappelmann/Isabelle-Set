theory int_1
  imports nat_1
begin

reserve n,m,k for Nat

mdef int_0_def_1 (infix "--" 110) where
  mlet "n be Nat", "m be Nat"
  "func n -- m  \<rightarrow> object means
     \<lambda>it. it be Nat & (it +\<^sub>\<S>\<^sup>\<nat> m) = n if m c= n otherwise \<lambda>it. for k be Nat st (k +\<^sub>\<S>\<^sup>\<nat> n) =m holds  it = [{},k]"
proof-
  show "(m \<subseteq> n implies (\<exists>x : object. x be Nat & (x +\<^sub>\<S>\<^sup>\<nat> m) = n))
      \<and>(\<not> m \<subseteq> n \<longrightarrow> (\<exists>x : object. \<forall>k : Nat. (k +\<^sub>\<S>\<^sup>\<nat> n) = m \<longrightarrow> x = [{} , k]))"
  proof(intro conjI impI)
    assume "m c= n"
    then show "ex k be object st k be Nat & k+\<^sub>\<S>\<^sup>\<nat> m = n" using Add_6 Add_9 by ty_auto
  next 
    assume "\<not> m c= n"
    hence "n c= m" using ordinal1_def_5c by ty_auto
    then obtain k where [ty]:"k be Nat" and
      A1: "(n +\<^sub>\<S>\<^sup>\<nat> k) = m" using Add_9 by ty_auto
    show "\<exists>x : object. \<forall>k : Nat. (k +\<^sub>\<S>\<^sup>\<nat> n) = m \<longrightarrow> x = [{} , k]"
    proof(rule bexI[of _ "[{},k]"],intro ballI impI)
      fix K assume [ty]: "K be Nat"
      assume "(K +\<^sub>\<S>\<^sup>\<nat> n) = m"
      hence "n +\<^sub>\<S>\<^sup>\<nat> k = n +\<^sub>\<S>\<^sup>\<nat> K" using A1 Add_6 by ty_auto
      hence "k=K" using Add_11[of K k n] by ty_auto
      thus "[{} , k] = [{} , K]" by simp
    qed mauto
  qed
  fix x y
  show "(m \<subseteq> n \<and> (x be Nat & (x +\<^sub>\<S>\<^sup>\<nat> m) = n) \<and> (y be Nat & (y +\<^sub>\<S>\<^sup>\<nat> m) = n) \<longrightarrow> x = y) \<and>
        ( \<not> m \<subseteq> n \<and> (\<forall>k : Nat. (k +\<^sub>\<S>\<^sup>\<nat> n) = m \<longrightarrow> x = [{} , k]) \<and> 
                      (\<forall>k : Nat. (k +\<^sub>\<S>\<^sup>\<nat> n) = m \<longrightarrow> y = [{} , k]) \<longrightarrow> x = y)"
  proof(intro conjI impI)
    assume A: "m \<subseteq> n \<and> (x be Nat & (x +\<^sub>\<S>\<^sup>\<nat> m) = n) \<and> (y be Nat & (y +\<^sub>\<S>\<^sup>\<nat> m) = n)"
      hence "m +\<^sub>\<S>\<^sup>\<nat> x = m +\<^sub>\<S>\<^sup>\<nat> y" using Add_6 by ty_auto
      then show "x=y" using Add_11[of y x m] A by ty_auto
    next
      assume A: "\<not> m \<subseteq> n \<and> (\<forall>k : Nat. (k +\<^sub>\<S>\<^sup>\<nat> n) = m \<longrightarrow> x = [{} , k]) \<and> 
                         (\<forall>k : Nat. (k +\<^sub>\<S>\<^sup>\<nat> n) = m \<longrightarrow> y = [{} , k])"
      hence "n c= m" using ordinal1_def_5c by ty_auto
      then obtain k where [ty]:"k be Nat" and
      A1: "(n +\<^sub>\<S>\<^sup>\<nat> k) = m" using Add_9 by ty_auto
      hence "k +\<^sub>\<S>\<^sup>\<nat> n = m" using Add_6 Add_9 by ty_auto
      hence "x = [{} , k]" "y = [{} , k]" using A by ty_auto
      then show "x=y" by auto 
  qed
qed mauto

mtheorem int_0_th_1:
  "(n +\<^sub>\<S>\<^sup>\<nat> k) = m implies m -- n = k"
proof(standard)
  assume A: "n +\<^sub>\<S>\<^sup>\<nat> k = m"
  have A2: "n \<subseteq> m" using Add_10 A by ty_auto
  hence [ty]: "m -- n is Nat" and "(m -- n) +\<^sub>\<S>\<^sup>\<nat> n =m" using int_0_def_1[of m n] by ty_auto
  hence "n +\<^sub>\<S>\<^sup>\<nat> (m -- n) =m" using Add_6 by ty_auto
  then show "m--n = k" using Add_11[of k "m--n" n] A by ty_auto
qed

mtheorem int_0_th_2:
  "n +\<^sub>\<S>\<^sup>\<nat> k = m & k = {} implies n -- m = {}"
proof
  assume A1: "n +\<^sub>\<S>\<^sup>\<nat> k = m & k = {}"
  hence A2: "n=m" using Add_3 by ty_auto
  hence "m c= n" using xboole_0_def_10 by ty_auto
  hence A3[ty]:"n--m is Nat" and "(n -- m) +\<^sub>\<S>\<^sup>\<nat> m =n" using int_0_def_1[of n m] by ty_auto
  hence "m +\<^sub>\<S>\<^sup>\<nat> (n -- m) = n" using Add_6 by ty_auto
  hence "m +\<^sub>\<S>\<^sup>\<nat> (n -- m) = m +\<^sub>\<S>\<^sup>\<nat> k" using A1 A2 by auto
  then show "n -- m = {}" using Add_11[of k "n--m" m, OF _ A3] A1 A2 by ty_auto
qed

mtheorem int_0_th_3:
  "n +\<^sub>\<S>\<^sup>\<nat> k = m & k<>{} implies n -- m = [{},k]"
proof
  assume A1: "n +\<^sub>\<S>\<^sup>\<nat> k = m & k<>{}"
  hence "n in m" using Add_8 bexI[of _ k Nat] by ty_auto
  hence "\<not> m c= n" "k +\<^sub>\<S>\<^sup>\<nat> n = m" using A1 Add_6 ordinal1_th_1 by ty_auto
  then show "n--m = [{},k]" using int_0_def_1[of n m] by ty_auto
qed

mtheorem 
 mlet "k be object"
 "cluster [{},k] \<rightarrow> non natural"
proof(auto)
  assume [ty]: "[{},k] be natural"
  have H: "[{},k] = {{{},k}, {{}}}" using tarski_def_5[of "{}" k] by ty_auto
  have "{{},k} in [{},k]" using tarski_def_2 H by auto
  hence K: "{} in {{},k}" "{{},k} c= [{},k]" using tarski_def_2 ordinal1_def_2E all_set by ty_auto
  have "{} in [{},k]" using tarski_def_3E[OF _ _ K(2)] K(1) by infer_auto
  hence "{} = {{},k} or {} = {{}}" using H tarski_def_2 by auto 
  then show "False" using tarski_def_1[of "{}" "{}"] tarski_def_2[of "{}" k "{}"] xb by auto
qed

mtheorem int_0_th_4:
  "n -- m is Nat iff m c= n"
proof (standard,rule aaI)
  assume A1: "n--m is Nat" "not m c= n"
  hence "n in m" using ordinal1_th_12[of n m] by ty_auto
  then obtain k where [ty]:"k be Nat" and
    A2: "k<>{} & n+\<^sub>\<S>\<^sup>\<nat> k=m " using Add_8 by ty_auto
  hence "n--m = [{},k]" using int_0_th_3 by ty_auto
  then show False using A1 by infer_auto
next 
  assume "m c= n"
  then obtain k where [ty]:"k be Nat" and
    A2:"(m+\<^sub>\<S>\<^sup>\<nat> k)=n " using Add_9 by ty_auto 
  hence "n--m =k" using int_0_th_1 by ty_auto
  then show "n--m is Nat" by ty_simp
qed

mtheorem int_0_th_5:
  "n -- k = n -- m implies k  = m"
proof(standard,cases " k c= n" )
  assume A0: "n -- k = n -- m"
  case T: True
  then obtain w where [ty]: "w be Nat" and 
      A1: "k +\<^sub>\<S>\<^sup>\<nat> w =n" using Add_9 by ty_auto
  hence A2: "n--k = w" using int_0_th_1 by ty_auto
  hence "n--m is Nat" using A0 by ty_simp
  hence "m c= n" using int_0_th_4 by ty_auto
  hence "(n--m)+\<^sub>\<S>\<^sup>\<nat> m = n" "(n--k)+\<^sub>\<S>\<^sup>\<nat> k = n" using T int_0_def_1 by ty_auto
  hence "w +\<^sub>\<S>\<^sup>\<nat> k = w+\<^sub>\<S>\<^sup>\<nat> m" using A0 A2 by auto
  then show "k=m" using Add_11[of k m w] by ty_auto
next 
  assume A0: "n -- k = n -- m"
  case T: False
  hence "n in k" using ordinal1_th_12[of n k] by ty_auto
  then obtain w where [ty]: "w be Nat" and 
    A1: "w<>{} & n +\<^sub>\<S>\<^sup>\<nat> w =k" using Add_8 by ty_auto
  hence A3: "n--k = [{},w]" using T int_0_th_3 by ty_auto
  hence A2: "not n -- m is Nat" using A0 by infer_auto

  have T1: "not m c= n"
  proof
    assume "m c= n"
    then obtain w where [ty]: "w be Nat" and 
      B1: "m +\<^sub>\<S>\<^sup>\<nat> w =n" using Add_9 by ty_auto
    hence "n--m =w" using int_0_th_1 by ty_auto
    then show False using A2 by ty_auto
  qed
   hence "n in m" using ordinal1_th_12[of n m] by ty_auto
  then obtain r where [ty]: "r be Nat" and 
    A4: "r<>{} & n +\<^sub>\<S>\<^sup>\<nat> r =m" using Add_8 by ty_auto
  hence "n -- m = [{},r]" using T1 int_0_th_3 by ty_auto
  hence "w=r" using A3 A0 xtuple_0_th_1a by auto
  then show "k=m" using A1 A4 by simp
qed

text_raw {*\DefineSnippet{INT}{*}
mdef numbers_def_4 ("INT") where
 "func INT \<rightarrow> set equals 
     NAT\<union>[:{0\<^sub>\<S>},NAT:] \\ {[0\<^sub>\<S>,0\<^sub>\<S>]}" 
text_raw {*}%EndSnippet*}
  by ty_auto

mtheorem 
  "cluster INT \<rightarrow> non empty"
proof
  have "{} is Nat" by mauto 
  hence "{} in NAT" using ordinal1_def_12 by auto
  then show "INT is non empty" unfolding numbers_def_4 using xboole_0_def_3 xboole_0_def_1 by ty_auto
qed

mdef int_1_def_2 ("integer") where
  "attr integer for object means (\<lambda>it . it in INT)"..

mtheorem
  "cluster integer for object"
proof
  have "{} is Nat" by mauto 
  hence "{} in NAT" using ordinal1_def_12 by auto
  hence "{} in INT" unfolding numbers_def_4 using xboole_0_def_3 by infer_auto
  thus "inhabited(integer \<bar> object)" using inhabited_def int_1_def_2 by auto
qed

abbreviation
  "Integer \<equiv> integer\<bar>object"

mtheorem cl_nat_int:
  "cluster natural \<rightarrow> integer for object"
proof(auto)
  fix it assume "it be natural"
  hence "it in NAT" using ordinal1_def_12 by auto
  hence "it in INT" unfolding numbers_def_4 using xboole_0_def_3 all_set by auto 
  then show "it be integer" using int_1_def_2 by auto
qed

reserve x for object 

mtheorem int_1_th_1:
  "x is Integer iff x is Nat or (ex k be Nat st k\<noteq>{} & x = [{},k])" 
proof(rule iffI3)
  show "x is Integer implies x is Nat or (ex k be Nat st k\<noteq>{} & x = [{},k])"
  proof(standard,rule disjCI2)
    assume A1: "x is Integer"  "\<not> x be Nat"
    hence "x in INT" "\<not> x in NAT" using int_1_def_2[of x] ordinal1_def_12[of x] all_set by ty_auto
    hence A2: "x in [:{ {} },NAT:] & not x in { [{},{}] }" unfolding numbers_def_4 using xboole_0_def_3
       xboole_0_def_5 by infer_auto
    then obtain y z where
       A3: "y in {{}} & z in NAT & x=[y,z]" using zfmisc_1_def_2 by infer_auto
    hence [ty]:"z be Nat" using ordinal1_def_12 all_set by auto
    have A4: "y = {}" "not x = [{},{}]" using A2 A3 tarski_def_1 by auto
    hence "not z = {}" using A3 xtuple_0_th_1[of y z] by auto
    then show "ex k be Nat st k\<noteq>{} & x = [{},k]" using A3 A4 bexI[of _ z Nat] by ty_auto
  qed
  assume A1: "x be Nat \<or> (\<exists>k : Nat. k \<noteq> {} \<and> x = [{} , k])"
  show "x is Integer"
  proof(cases "x be Nat")
    case True
    hence "x in NAT" using ordinal1_def_12 by auto
    hence "x in INT" unfolding  numbers_def_4 using xboole_0_def_3 by infer_auto
    thus "x is Integer" using int_1_def_2 by ty_auto
  next
    case False
    then obtain k where [ty]: "k be Nat" and
       A2:"k\<noteq>{} \<and> x = [{},k]" using A1 by auto
    hence "x\<noteq> [{},{}]" using xtuple_0_th_1[of "{}" "{}" "{}" k] by ty_auto
    hence A3: "not x in {[{},{}]}" using tarski_def_1 by auto
    have "{} in {{}} & k in NAT" using tarski_def_1 ordinal1_def_12[of k] by ty_auto
    hence "x in [:{{}},NAT:]" using zfmisc_1_def_2 A2 by infer_auto
    hence "x in [:{{}},NAT:]\\{[{},{}]}" using A3 xboole_0_def_5 by infer_auto
    hence "x in INT" unfolding numbers_def_4 using xboole_0_def_3 by infer_auto
    thus "x is Integer" using int_1_def_2 by ty_auto
  qed
qed

mtheorem pair_int:
  "k<>{} implies [{},k] is Integer"
proof
  assume "k<>{}"
  hence "ex n be Nat st n\<noteq>{} & [{},k] = [{},n]" using bexI[of _ k Nat] by ty_auto
  then show "[{},k] is Integer" using int_1_th_1 by auto
qed


mtheorem
  mlet "i be Nat", "j be Nat" 
  "cluster i--j \<rightarrow> Integer"
proof(standard,cases "j c= i")
  case T: True
    then obtain k where TY[ty]:"k be Nat" and
      A1: "j +\<^sub>\<S>\<^sup>\<nat> k = i" using Add_9 by ty_auto
    hence "i -- j = k" using int_0_th_1[ of i k j] T by ty_auto
    then show "i -- j be Integer"  using int_1_th_1[of k] by ty_auto
  next
  case F: False
    hence "i in j" using ordinal1_th_12[of i j] by ty_auto
    then obtain k where TY[ty]:"k be Nat" and
      A1: "k <> {} & i +\<^sub>\<S>\<^sup>\<nat> k = j" using Add_8 by ty_auto
    hence A2: "i -- j = [{},k]" using int_0_def_1[of i j] F Add_6[of i k] by ty_auto
    have "[{},k] is Integer" using int_1_th_1[of "[{},k]"] A1 bexI[of _ k Nat] by ty_auto
    then show "i -- j be Integer"  using A2 by ty_auto
qed

reserve k,k1,k2 for Nat  

reserve i,j,i1,i2,i3 for Integer

mdef int_1_def_3 ("_ +\<^sub>\<S>\<^sup>\<int> _" [101,100] 100) where
  mlet "i be Integer","j be Integer"
  "func i +\<^sub>\<S>\<^sup>\<int> j \<rightarrow> Integer means
      \<lambda>it . (i +\<^sub>\<S>\<^sup>\<nat> j) = it  if i is Nat & j is Nat,  
      \<lambda>it . for k st i = [{},k] holds it = j -- k if not i is Nat & j is Nat,
      \<lambda>it . for k st j = [{},k] holds it = i -- k if i is Nat & not j is Nat otherwise
          \<lambda>it . for k1, k2 st i = [{},k1] & j = [{},k2] holds it = [{},k1 +\<^sub>\<S>\<^sup>\<nat> k2]"
proof-
  show "(i is Nat \<and> j is Nat \<longrightarrow> (\<exists>x : Integer. i +\<^sub>\<S>\<^sup>\<nat> j = x)) \<and>
    (\<not> i is Nat \<and> j is Nat \<longrightarrow> (\<exists>x : Integer. \<forall>k : Nat. i = [{} , k] \<longrightarrow> x = j -- k)) \<and>
    (i is Nat \<and> \<not> j is Nat  \<longrightarrow> (\<exists>x : Integer. \<forall>k : Nat. j = [{} , k] \<longrightarrow> x = i -- k)) \<and>
    (\<not> (i is Nat \<and> j is Nat) \<and> \<not> (\<not> i is Nat \<and> j is Nat) \<and> \<not> (i is Nat \<and> \<not> j is Nat) \<longrightarrow>
     (\<exists>x : Integer. \<forall>k1 : Nat. \<forall>k2 : Nat. i = [{} , k1] \<and> j = [{} , k2] \<longrightarrow> x = [{} , k1 +\<^sub>\<S>\<^sup>\<nat> k2]))"
  proof(intro conjI impI)
    assume [ty]: "i be Nat \<and> j be Nat"
    have "(i +\<^sub>\<S>\<^sup>\<nat> j) is Integer" using int_1_th_1 by infer_auto
    then show "\<exists>x : Integer. i +\<^sub>\<S>\<^sup>\<nat> j = x" by ty_auto
  next
    assume A1:"\<not> i is Nat \<and> j is Nat"
    then obtain m where [ty]: "m be Nat" and
      A2: "m<>{} & i = [{},m]" using int_1_th_1[of i] by ty_auto
    have [ty]: " j be Nat" using A1 by simp
    show "\<exists>x : Integer. \<forall>k : Nat. i = [{} , k] \<longrightarrow> x = j -- k"
    proof(rule bexI[of _ "j--m"],standard,standard)
      fix k assume [ty]:"k be Nat" and "i = [{} , k]"
      then show "j -- m = j -- k" using xtuple_0_th_1a A2 by auto
    qed mauto
  next    
    assume A1:" i is Nat \<and> \<not> j is Nat"
    then obtain m where [ty]: "m be Nat" and
      A2: "m<>{} & j = [{},m]" using int_1_th_1[of j] by ty_auto
    have [ty]: " i be Nat" using A1 by simp
    show "\<exists>x : Integer. \<forall>k : Nat. j = [{} , k] \<longrightarrow> x = i -- k"
    proof(rule bexI[of _ "i--m"],standard,standard)
      fix k assume [ty]:"k be Nat" and "j = [{} , k]"
      then show "i -- m = i -- k" using xtuple_0_th_1a A2 by auto
    qed mauto
  next 
    assume A1: "\<not> (i is Nat \<and> j is Nat) \<and> \<not> (\<not> i is Nat \<and> j is Nat) \<and> \<not> (i is Nat \<and> \<not> j is Nat)"
    then obtain m where [ty]: "m be Nat" and
      A2: "m<>{} & i = [{},m]" using int_1_th_1[of i] by ty_auto
    then obtain n where [ty]: "n be Nat" and
      A3: "n<>{} & j = [{},n]" using int_1_th_1[of j] A1 by ty_auto   
    have "m +\<^sub>\<S>\<^sup>\<nat> n <>{}" using Add_14[of n m] A2 A3 by ty_auto
    hence "ex k be Nat st k\<noteq>{} & [{},m +\<^sub>\<S>\<^sup>\<nat> n] = [{},k]" using bexI[of _ "m +\<^sub>\<S>\<^sup>\<nat> n" Nat] by infer_auto
    hence [ty]: "[{},m +\<^sub>\<S>\<^sup>\<nat> n] is Integer" using  int_1_th_1 by auto
    show "\<exists>x : Integer. \<forall>k1 : Nat. \<forall>k2 : Nat. i = [{} , k1] \<and> j = [{} , k2] \<longrightarrow> x = [{} , (k1 +\<^sub>\<S>\<^sup>\<nat> k2)]"
    proof(rule bexI[of _ "[{},m +\<^sub>\<S>\<^sup>\<nat> n]"], intro ballI impI)
      fix k1 k2 assume [ty]:"k1 be Nat" "k2 be Nat" and
        A4:"i = [{} , k1] \<and> j = [{} , k2]"
      hence "m=k1" "n=k2" using A2 A3 xtuple_0_th_1a by auto
      then show "[{} , m +\<^sub>\<S>\<^sup>\<nat> n] = [{} , k1 +\<^sub>\<S>\<^sup>\<nat> k2]" by simp
    qed mauto
  qed
  fix x y assume [ty]: "x be Integer" "y be Integer"
  show" ((i be Nat \<and> j be Nat) \<and> (i +\<^sub>\<S>\<^sup>\<nat> j) = x \<and> (i +\<^sub>\<S>\<^sup>\<nat> j) = y \<longrightarrow> x = y) \<and>
           ((\<not> i be Nat \<and> j be Nat) \<and> (\<forall>k : Nat. i = [{} , k] \<longrightarrow> x = j -- k) \<and> (\<forall>k : Nat. i = [{} , k] \<longrightarrow> y = j -- k) \<longrightarrow> x = y) \<and>
           ((i be Nat \<and> \<not> j be Nat) \<and> (\<forall>k : Nat. j = [{} , k] \<longrightarrow> x = i -- k) \<and> (\<forall>k : Nat. j = [{} , k] \<longrightarrow> y = i -- k) \<longrightarrow> x = y) \<and>
           (\<not> (i be Nat \<and> j be Nat) \<and>
            \<not> (\<not> i be Nat \<and> j be Nat) \<and>
            \<not> (i be Nat \<and> \<not> j be Nat) \<and>
            (\<forall>k1 : Nat. \<forall>k2 : Nat. i = [{} , k1] \<and> j = [{} , k2] \<longrightarrow> x = [{} , k1 +\<^sub>\<S>\<^sup>\<nat> k2]) \<and>
            (\<forall>k1 : Nat. \<forall>k2 : Nat. i = [{} , k1] \<and> j = [{} , k2] \<longrightarrow> y = [{} , k1 +\<^sub>\<S>\<^sup>\<nat> k2]) \<longrightarrow>
            x = y)"
  proof(intro conjI impI)
    show "(i be Nat \<and> j be Nat) \<and> (i +\<^sub>\<S>\<^sup>\<nat> j) = x \<and> (i +\<^sub>\<S>\<^sup>\<nat> j) = y \<Longrightarrow> x = y" by auto
  next
    assume A1: " (\<not> i be Nat \<and> j be Nat) \<and> (\<forall>k : Nat. i = [{} , k] \<longrightarrow> x = j -- k) \<and> (\<forall>k : Nat. i = [{} , k] \<longrightarrow> y = j -- k)"
    then obtain m where [ty]: "m be Nat" and
      A2: "m<>{} & i = [{},m]" using int_1_th_1[of i] by ty_auto
    hence "x = j--m" "y = j--m" using A1 by auto
    then show "x = y" using A1 by auto
  next 
    assume A1: "(i be Nat \<and> \<not> j be Nat) \<and> (\<forall>k : Nat. j = [{} , k] \<longrightarrow> x = i -- k) \<and> (\<forall>k : Nat. j = [{} , k] \<longrightarrow> y = i -- k)"
      then obtain m where [ty]: "m be Nat" and
      A2: "m<>{} & j = [{},m]" using int_1_th_1[of j] by ty_auto
    hence "x = i--m" "y = i--m" using A1 by auto
    then show "x = y" using A1 by auto
  next
    assume A1: "\<not> (i be Nat \<and> j be Nat) \<and>
            \<not> (\<not> i be Nat \<and> j be Nat) \<and>
            \<not> (i be Nat \<and> \<not> j be Nat) \<and>
            (\<forall>k1 : Nat. \<forall>k2 : Nat. i = [{} , k1] \<and> j = [{} , k2] \<longrightarrow> x = [{} , (k1 +\<^sub>\<S>\<^sup>\<nat> k2)]) \<and>
            (\<forall>k1 : Nat. \<forall>k2 : Nat. i = [{} , k1] \<and> j = [{} , k2] \<longrightarrow> y = [{} , (k1 +\<^sub>\<S>\<^sup>\<nat> k2)])"
    then obtain m1 where [ty]: "m1 be Nat" and
      A2: "m1<>{} & i = [{},m1]" using int_1_th_1[of i] by ty_auto
    obtain m2 where [ty]: "m2 be Nat" and
      A3: "m2<>{} & j = [{},m2]" using int_1_th_1[of j] A1 by ty_auto 
    hence "x = [{} , (m1 +\<^sub>\<S>\<^sup>\<nat> m2)]" "y = [{} , (m1 +\<^sub>\<S>\<^sup>\<nat> m2)]"  using A2 A1 by ty_auto
    then show "x=y" by simp
  qed
qed mauto


mtheorem
  mlet "i be Nat", "j be Nat"
  "cluster i +\<^sub>\<S>\<^sup>\<int> j \<rightarrow> Nat"
proof
  have "i +\<^sub>\<S>\<^sup>\<int> j = i +\<^sub>\<S>\<^sup>\<nat> j" using int_1_def_3 by ty_auto
  then show "i +\<^sub>\<S>\<^sup>\<int> j is Nat" by infer_auto
qed

mtheorem int_1_th_2:
  "i +\<^sub>\<S>\<^sup>\<int> {} = i & {} +\<^sub>\<S>\<^sup>\<int> i = i"
proof(cases "i is Nat")
  case T:True
  hence "i +\<^sub>\<S>\<^sup>\<int> {} = i +\<^sub>\<S>\<^sup>\<nat> {}" "{} +\<^sub>\<S>\<^sup>\<int> i = {} +\<^sub>\<S>\<^sup>\<nat> i"  using int_1_def_3 by ty_auto
  then show "i +\<^sub>\<S>\<^sup>\<int> {} = i & {} +\<^sub>\<S>\<^sup>\<int> i = i" using Add_3 Add_4 T by ty_auto
next
  case F:False
  then obtain  k where [ty]: "k be Nat" and
     A1:"k\<noteq>{} & i = [{},k]" using int_1_th_1[of i] by ty_auto
  hence A2: "i +\<^sub>\<S>\<^sup>\<int> {} = {} -- k" "{} +\<^sub>\<S>\<^sup>\<int> i = {}--k" 
    using int_1_def_3[of i "{}",simplified] int_1_def_3[of "{}" i,simplified] F  by infer_auto
  have "{} +\<^sub>\<S>\<^sup>\<nat> k = k" using Add_4 by ty_auto
  then show "i +\<^sub>\<S>\<^sup>\<int> {} = i & {} +\<^sub>\<S>\<^sup>\<int> i = i" using A2 A1 int_0_th_3[of k k "{}"] by ty_auto
qed

mtheorem int_1_th_3:
  "k <> {}  implies k +\<^sub>\<S>\<^sup>\<int> [{},k] = {} & [{},k] +\<^sub>\<S>\<^sup>\<int> k = {} "
proof(rule impI)
  assume "k<>{}"
  hence [ty]: "[{}, k] is Integer" using int_1_th_1[of "[{},k]"] bexI[of _ k Nat] by ty_auto
  have "k +\<^sub>\<S>\<^sup>\<int> [{},k] = k--k" "[{},k] +\<^sub>\<S>\<^sup>\<int> k = k--k"
    using int_1_def_3[of "[{},k]" k,simplified] using int_1_def_3[of k "[{},k]",simplified] by ty_auto
  then show " k +\<^sub>\<S>\<^sup>\<int> [{},k] = {} & [{},k] +\<^sub>\<S>\<^sup>\<int> k = {}" using  int_0_th_1[OF _ _ _ Add_3[of k],simplified] by ty_auto
qed

mtheorem int_1_th_4:
  "ex j st i +\<^sub>\<S>\<^sup>\<int> j = {} & j +\<^sub>\<S>\<^sup>\<int> i = {}"
proof(cases "i is Nat")
  case [ty]: True
    show "ex j st i +\<^sub>\<S>\<^sup>\<int> j = {} & j +\<^sub>\<S>\<^sup>\<int> i = {}"
    proof(cases "i={}")
      case True
      then show ?thesis using int_1_th_2 bexI[of _ "{}" Integer] by ty_auto
    next case F: False
      hence [ty]:"[{} , i] be integer" using pair_int by ty_auto
      hence " i +\<^sub>\<S>\<^sup>\<int> [{},i] = {} & [{},i] +\<^sub>\<S>\<^sup>\<int> i = {}" using int_1_th_3[of i,simplified] F by ty_auto
      then show ?thesis using bexI[of _ "[{},i]" Integer,simplified] by ty_auto
    qed
  next 
    case False
    then obtain k where [ty]: "k be Nat" and
      A1: "k<>{} & i=[{},k]" using int_1_th_1[of i] by ty_auto
    have [ty]: "k be integer" by ty_auto
    hence [ty]:"[{} , k] be integer" using pair_int A1 by ty_auto
    hence " k +\<^sub>\<S>\<^sup>\<int> [{},k] = {} & [{},k] +\<^sub>\<S>\<^sup>\<int> k = {}" using int_1_th_3[of k,simplified] A1  by ty_auto
    then show ?thesis using  bexI[of _ k Integer,simplified] A1 by ty_auto
  qed

mtheorem int_1_th_5:
 "i +\<^sub>\<S>\<^sup>\<int> j = j +\<^sub>\<S>\<^sup>\<int> i"
proof(cases "i is Nat")
  case T1[ty]: True
  show"i +\<^sub>\<S>\<^sup>\<int> j = j +\<^sub>\<S>\<^sup>\<int> i"
    proof(cases "j is Nat")
      case T2[ty]: True
      hence "i+\<^sub>\<S>\<^sup>\<int> j = i+\<^sub>\<S>\<^sup>\<nat> j" "j+\<^sub>\<S>\<^sup>\<int> i = j+\<^sub>\<S>\<^sup>\<nat> i" using int_1_def_3 by ty_auto
      then show "i +\<^sub>\<S>\<^sup>\<int> j = j +\<^sub>\<S>\<^sup>\<int> i" using Add_6 by ty_auto
    next
      case F2[ty]:False
         then obtain k where [ty]: "k be Nat" and
           A1: "k<>{} & j=[{},k]" using int_1_th_1[of j] by ty_auto
         hence "j+\<^sub>\<S>\<^sup>\<int> i = i -- k" "i+\<^sub>\<S>\<^sup>\<int> j = i -- k" using 
           int_1_def_3[of j i,simplified] int_1_def_3[of i j,simplified] by infer_auto
         then show "i +\<^sub>\<S>\<^sup>\<int> j = j +\<^sub>\<S>\<^sup>\<int> i" using A1 int_1_def_3[of i j,simplified] by ty_auto
    qed
  next
    case F1: False
      then obtain k where [ty]: "k be Nat" and
        A1: "k<>{} & i=[{},k]" using int_1_th_1[of i] by ty_auto
      show"i +\<^sub>\<S>\<^sup>\<int> j = j +\<^sub>\<S>\<^sup>\<int> i"
        proof(cases "j is Nat")
          case T2[ty]:True
            hence "j+\<^sub>\<S>\<^sup>\<int> i = j -- k" "i+\<^sub>\<S>\<^sup>\<int> j = j -- k" using 
            int_1_def_3[of j i,simplified] int_1_def_3[of i j,simplified] A1 by infer_auto
            then show "i +\<^sub>\<S>\<^sup>\<int> j = j +\<^sub>\<S>\<^sup>\<int> i" using A1 int_1_def_3[of i j,simplified] by ty_auto
          next
            case F2:False
              then obtain n where [ty]: "n be Nat" and
                A2: "n<>{} & j=[{},n]" using int_1_th_1[of j] by ty_auto
              have "i +\<^sub>\<S>\<^sup>\<int> j = [{}, (k +\<^sub>\<S>\<^sup>\<nat> n)]" "j +\<^sub>\<S>\<^sup>\<int> i = [{}, (n +\<^sub>\<S>\<^sup>\<nat> k)]" using 
               int_1_def_3[of i j, simplified] int_1_def_3[of j i, simplified] A1 A2 by inst_nopass_auto
              then show "i +\<^sub>\<S>\<^sup>\<int> j = j +\<^sub>\<S>\<^sup>\<int> i" using Add_6 by ty_auto
    qed
qed

mtheorem int_1_th_6:
  "(k +\<^sub>\<S>\<^sup>\<int> k1) -- k2 = k +\<^sub>\<S>\<^sup>\<int> (k1 -- k2)" 
proof(cases " k2 c= k +\<^sub>\<S>\<^sup>\<int> k1")
  case T1:True
    then obtain w where [ty]: "w be Nat" and
      A1: "k2 +\<^sub>\<S>\<^sup>\<nat> w = (k +\<^sub>\<S>\<^sup>\<int> k1)" using Add_9 by ty_auto
    have A2: "k+\<^sub>\<S>\<^sup>\<int> k1 = k +\<^sub>\<S>\<^sup>\<nat> k1" using int_1_def_3 by ty_auto
    have A3: "(k +\<^sub>\<S>\<^sup>\<int> k1) -- k2 = w" using A1 int_0_th_1 by ty_auto
    show "(k +\<^sub>\<S>\<^sup>\<int> k1) -- k2 = k +\<^sub>\<S>\<^sup>\<int> (k1 -- k2)"
      proof(cases "k2 c= k1")
        case T2:True
          then obtain n where [ty]: "n be Nat" and
             A4: "k2 +\<^sub>\<S>\<^sup>\<nat> n = k1" using Add_9 by ty_auto
          hence "k1 -- k2 = n" using int_0_th_1 by ty_auto
          hence A5: "k +\<^sub>\<S>\<^sup>\<int> (k1 -- k2) = k +\<^sub>\<S>\<^sup>\<nat> n" using int_1_def_3[of k n] by ty_auto 

          have  "k2 +\<^sub>\<S>\<^sup>\<nat> w = (k +\<^sub>\<S>\<^sup>\<nat> k2) +\<^sub>\<S>\<^sup>\<nat> n" using A1 A2 A4 Add_7 by ty_auto
          hence "k2 +\<^sub>\<S>\<^sup>\<nat> (k +\<^sub>\<S>\<^sup>\<nat> n) = k2 +\<^sub>\<S>\<^sup>\<nat> w" using Add_6[of k2 k] Add_7 by ty_auto
          hence "w = k+\<^sub>\<S>\<^sup>\<nat> n" using Add_11[of w "k+\<^sub>\<S>\<^sup>\<nat> n" k2] by infer_auto
          then show ?thesis using A3 A5 by simp
        next 
          case False
            hence "k1 in k2" using ordinal1_th_12[of k1 k2] by ty_auto
            then obtain n where [ty]: "n be Nat" and
             A4: "n <>{} & k1 +\<^sub>\<S>\<^sup>\<nat> n = k2" using Add_8 by ty_auto
            have [ty]: "[{},n] is Integer" using A4 pair_int by ty_auto                                  
            have "k1 -- k2 = [{},n]" using A4 int_0_th_3 by ty_auto
            hence A5: "k +\<^sub>\<S>\<^sup>\<int> (k1 -- k2) = k -- n" using int_1_def_3[of k "[{},n]",simplified] by ty_auto

            have  "k1 +\<^sub>\<S>\<^sup>\<nat> (n +\<^sub>\<S>\<^sup>\<nat> w) = k1 +\<^sub>\<S>\<^sup>\<nat> k" using A1 A2 A4 Add_7 Add_6[of k k1] by ty_auto
            hence "n +\<^sub>\<S>\<^sup>\<nat> w = k" using Add_11[of k "n +\<^sub>\<S>\<^sup>\<nat> w" k1,simplified] by infer_auto
            hence "k--n = w" using int_0_th_1 by ty_auto
          then show ?thesis using A3 A5 by simp
        qed
    next
      case F1:False
        hence "k +\<^sub>\<S>\<^sup>\<int> k1 in k2" using ordinal1_th_12[of "k +\<^sub>\<S>\<^sup>\<int> k1" k2] F1 by ty_auto
        then obtain n where [ty]: "n be Nat" and
        A1: "n <>{} & (k +\<^sub>\<S>\<^sup>\<int> k1)+\<^sub>\<S>\<^sup>\<nat> n = k2" using Add_8 by ty_auto
        have A2: "(k +\<^sub>\<S>\<^sup>\<int> k1) -- k2 = [{},n]" using A1 int_0_th_3 by ty_auto
        have A3: "k +\<^sub>\<S>\<^sup>\<nat> n <>{}" using Add_14[of n k] A1 by ty_auto
        hence [ty]: "[{},(k +\<^sub>\<S>\<^sup>\<nat> n)] is Integer" using pair_int by infer_auto
        have "k2 = (k1 +\<^sub>\<S>\<^sup>\<nat> k)+\<^sub>\<S>\<^sup>\<nat> n" using A1 int_1_def_3[of k k1,simplified] Add_6[of k k1] by ty_auto
        hence "k2 = k1 +\<^sub>\<S>\<^sup>\<nat> (k +\<^sub>\<S>\<^sup>\<nat> n)" using Add_7 by ty_auto
        hence "k1 -- k2 = [{},(k +\<^sub>\<S>\<^sup>\<nat> n)]" using A3 int_0_th_3 by infer_auto
        hence "k +\<^sub>\<S>\<^sup>\<int> (k1 -- k2) = k -- (k +\<^sub>\<S>\<^sup>\<nat> n)" using int_1_def_3[of k "[{},(k +\<^sub>\<S>\<^sup>\<nat> n)]",simplified] by ty_auto
        then show "(k +\<^sub>\<S>\<^sup>\<int> k1) -- k2  = k +\<^sub>\<S>\<^sup>\<int> (k1 -- k2)" using A1 A2 A3 int_0_th_3[of "k +\<^sub>\<S>\<^sup>\<nat> n" n] by ty_auto 
      qed

mtheorem int_1_th_7:
  "not i is Nat implies (k1 +\<^sub>\<S>\<^sup>\<int> k2) +\<^sub>\<S>\<^sup>\<int> i = k1 +\<^sub>\<S>\<^sup>\<int> (k2 +\<^sub>\<S>\<^sup>\<int> i)"
proof
  assume "not i is Nat" 
 then obtain k3 where [ty]: "k3 be Nat" and
    A1: "k3<>{} & i=[{},k3]" using int_1_th_1[of i] by ty_auto
 have [ty]: "k1 +\<^sub>\<S>\<^sup>\<int> k2 is Nat" by ty_auto

 have "(k1 +\<^sub>\<S>\<^sup>\<int> k2) +\<^sub>\<S>\<^sup>\<int> i = (k1 +\<^sub>\<S>\<^sup>\<int> k2) -- k3" using int_1_def_3[of "k1 +\<^sub>\<S>\<^sup>\<int> k2" i,simplified] A1 by infer_auto
   also have "...= k1 +\<^sub>\<S>\<^sup>\<int> (k2 -- k3)" using int_1_th_6 by ty_auto
   also have "\<dots>=k1 +\<^sub>\<S>\<^sup>\<int> (k2 +\<^sub>\<S>\<^sup>\<int> i) " using int_1_def_3[of k2 i,simplified] A1 by infer_auto
  finally show "(k1 +\<^sub>\<S>\<^sup>\<int> k2) +\<^sub>\<S>\<^sup>\<int> i = k1 +\<^sub>\<S>\<^sup>\<int> (k2 +\<^sub>\<S>\<^sup>\<int> i)" by auto
qed


mtheorem int_1_th_8:
  "not i1 is Nat & not i2 is Nat implies (k +\<^sub>\<S>\<^sup>\<int> i1) +\<^sub>\<S>\<^sup>\<int> i2 = k +\<^sub>\<S>\<^sup>\<int> (i1 +\<^sub>\<S>\<^sup>\<int> i2)"
proof
  assume A0: "not i1 is Nat & not i2 is Nat"
  then obtain k1 where [ty]: "k1 be Nat" and
    A1: "k1<>{} & i1=[{},k1]" using int_1_th_1[of i1] by ty_auto
  then obtain k2 where [ty]: "k2 be Nat" and
    A2: "k2<>{} & i2=[{},k2]" using int_1_th_1[of i2] A0 by ty_auto
  have A3: "k +\<^sub>\<S>\<^sup>\<int> i1 = k -- k1" using int_1_def_3[of k i1,simplified] A1 by infer_auto
  have A4: "i1 +\<^sub>\<S>\<^sup>\<int> i2 = [{}, k1 +\<^sub>\<S>\<^sup>\<nat> k2]"
    using int_1_def_3[of i1 i2,simplified] A1 A2 by infer_auto
  hence A5: "k +\<^sub>\<S>\<^sup>\<int> (i1 +\<^sub>\<S>\<^sup>\<int> i2) = k -- (k1 +\<^sub>\<S>\<^sup>\<nat> k2)" using int_1_def_3[of k "i1 +\<^sub>\<S>\<^sup>\<int> i2",simplified] by infer_auto
  show "(k +\<^sub>\<S>\<^sup>\<int> i1) +\<^sub>\<S>\<^sup>\<int> i2 = k +\<^sub>\<S>\<^sup>\<int> (i1 +\<^sub>\<S>\<^sup>\<int> i2)"
  proof(cases "k1 c= k")
    case True
      then obtain w1 where [ty]: "w1 be Nat" and
        B1: "k1 +\<^sub>\<S>\<^sup>\<nat> w1 = k" using Add_9 by ty_auto
      hence C1: "k -- k1 = w1" using int_0_th_1 by ty_auto
      show ?thesis
      proof(cases "k2 c= w1")
        case True
          then obtain w2 where [ty]: "w2 be Nat" and
            B2: "k2 +\<^sub>\<S>\<^sup>\<nat> w2 = w1" using Add_9 by ty_auto
          hence "w1 -- k2 = w2" using int_0_th_1 by ty_auto
          hence C2: "w1 +\<^sub>\<S>\<^sup>\<int> i2 = w2" using int_1_def_3[of w1 i2,simplified] A2 by infer_auto
          have "(k1 +\<^sub>\<S>\<^sup>\<nat> k2) +\<^sub>\<S>\<^sup>\<nat> w2 = k" using B1 B2 Add_7[of w2 k2] by ty_auto
          hence "k -- (k1 +\<^sub>\<S>\<^sup>\<nat> k2) = w2" using int_0_th_1 by infer_auto
          then show ?thesis using A3 A5 B1 C1 C2 by auto
        next
        case False
          hence "w1 in k2" using ordinal1_th_12[of w1 k2] by ty_auto
          then obtain w2 where [ty]: "w2 be Nat" and
            B2: "w2 <>{} & k2 = w1 +\<^sub>\<S>\<^sup>\<nat> w2" using Add_8[of k2 w1] by ty_auto
          have [ty]: "[{},w2] is Integer" using pair_int B2 by ty_auto
          have "w1 -- k2 = [{},w2]" using int_0_th_3 B2 by infer_auto
          hence C2: "w1 +\<^sub>\<S>\<^sup>\<int> i2 = [{},w2]" using int_1_def_3[of w1 i2,simplified] A2 by infer_auto
          have [ty]:"(k1 +\<^sub>\<S>\<^sup>\<nat> k2) is Nat" by infer_auto
          have " k +\<^sub>\<S>\<^sup>\<nat> w2 = k1 +\<^sub>\<S>\<^sup>\<nat> (w1 +\<^sub>\<S>\<^sup>\<nat> w2)" using B1 Add_7[of w2 w1 k1]  by ty_auto
          hence "k -- (k1 +\<^sub>\<S>\<^sup>\<nat> k2) = [{},w2]" using int_0_th_3[of "k1 +\<^sub>\<S>\<^sup>\<nat> k2" w2 k,simplified] B2 by infer_auto
          then show ?thesis using A3 C1 C2 A5 by auto
        qed
      next
        case False
          hence "k in k1" using ordinal1_th_12[of k k1] by ty_auto
          then obtain w1 where [ty]: "w1 be Nat" and
            B2: "w1 <>{} & k1 = k +\<^sub>\<S>\<^sup>\<nat> w1" using Add_8[of k1 k] by ty_auto
          have [ty]: "[{},w1] is Integer" using pair_int B2 by ty_auto
          have [ty]: "(k1 +\<^sub>\<S>\<^sup>\<nat> k2) is Nat" "(w1 +\<^sub>\<S>\<^sup>\<nat> k2) is Nat" by infer_auto
          have "k -- k1 = [{},w1]" using int_0_th_3 B2 by infer_auto
          hence "(k +\<^sub>\<S>\<^sup>\<int> i1) +\<^sub>\<S>\<^sup>\<int> i2 = [{},w1] +\<^sub>\<S>\<^sup>\<int> [{},k2]" using A3 A2 by auto
          hence C2: "(k +\<^sub>\<S>\<^sup>\<int> i1) +\<^sub>\<S>\<^sup>\<int> i2 = [{},(w1 +\<^sub>\<S>\<^sup>\<nat> k2)]" using A3 A2 int_1_def_3[of "[{},w1]" i2,simplified]  by infer_auto
          have H1: "w1 +\<^sub>\<S>\<^sup>\<nat> k2 <>{}" using Add_14[of k2 w1] B2 by ty_auto
          have "k +\<^sub>\<S>\<^sup>\<nat> (w1 +\<^sub>\<S>\<^sup>\<nat> k2) = k1 +\<^sub>\<S>\<^sup>\<nat> k2" using B2 Add_7 by ty_auto
          hence "k -- (k1 +\<^sub>\<S>\<^sup>\<nat> k2) = [{},(w1 +\<^sub>\<S>\<^sup>\<nat> k2)]" using H1 int_0_th_3[of "k1 +\<^sub>\<S>\<^sup>\<nat> k2" "w1 +\<^sub>\<S>\<^sup>\<nat> k2" k,simplified] by ty_auto
          thus ?thesis using C2 A5 by auto 
      qed
qed

mtheorem int_1_th_9:
 "(i1 +\<^sub>\<S>\<^sup>\<int> i2) +\<^sub>\<S>\<^sup>\<int> i3 = i1 +\<^sub>\<S>\<^sup>\<int> (i2 +\<^sub>\<S>\<^sup>\<int> i3)"
proof(cases "i1 is Nat")
  case T1[ty]: True
  show ?thesis
     proof(cases "i2 is Nat")
       case T2[ty]: True
           show "(i1 +\<^sub>\<S>\<^sup>\<int> i2) +\<^sub>\<S>\<^sup>\<int> i3 = i1 +\<^sub>\<S>\<^sup>\<int> (i2 +\<^sub>\<S>\<^sup>\<int> i3)"
              proof(cases "i3 is Nat")
                case T3[ty]:True
                have "(i1 +\<^sub>\<S>\<^sup>\<int> i2) +\<^sub>\<S>\<^sup>\<int> i3 = (i1 +\<^sub>\<S>\<^sup>\<int> i2) +\<^sub>\<S>\<^sup>\<nat> i3" using int_1_def_3 by ty_auto
                  also have "...= (i1 +\<^sub>\<S>\<^sup>\<nat> i2) +\<^sub>\<S>\<^sup>\<nat> i3" using int_1_def_3 by ty_auto
                  also have "...= i1 +\<^sub>\<S>\<^sup>\<nat> (i2 +\<^sub>\<S>\<^sup>\<nat> i3)" using Add_7 by ty_auto
                  also have "...= i1 +\<^sub>\<S>\<^sup>\<nat> (i2 +\<^sub>\<S>\<^sup>\<int> i3)" using int_1_def_3 by ty_auto
                  also have "...= i1 +\<^sub>\<S>\<^sup>\<int> (i2 +\<^sub>\<S>\<^sup>\<int> i3)" using int_1_def_3 by ty_auto
                  finally show ?thesis by auto
               next
                 case F2: False
                 thus ?thesis using int_1_th_7 by ty_auto
                qed
     next
       case F2: False
             then obtain k2 where [ty]: "k2 be Nat" and
                   A1: "k2<>{} & i2=[{},k2]" using int_1_th_1[of i2] F2 by ty_auto
             have A2: "i1 +\<^sub>\<S>\<^sup>\<int> i2 = i1 -- k2" using int_1_def_3[of i1 i2,simplified] A1 by infer_auto
       show ?thesis
       proof(cases "i3 is Nat")
         case [ty]:True
                 have "(i1 +\<^sub>\<S>\<^sup>\<int> i2) +\<^sub>\<S>\<^sup>\<int> i3 = (i1 -- k2) +\<^sub>\<S>\<^sup>\<int> i3" using A2 by ty_auto
                 also have "...= i3 +\<^sub>\<S>\<^sup>\<int> (i1 -- k2)" using int_1_th_5 by infer_auto
                  also have "...= (i3 +\<^sub>\<S>\<^sup>\<int> i1) -- k2" using int_1_th_6[of k2 i1 i3,simplified] by ty_auto
                  also have "...= (i3 +\<^sub>\<S>\<^sup>\<int> i1) +\<^sub>\<S>\<^sup>\<int> i2"  using A1 int_1_def_3[of "i3 +\<^sub>\<S>\<^sup>\<int> i1" i2,simplified] by infer_auto
                   also have "...= (i1 +\<^sub>\<S>\<^sup>\<int> i3) +\<^sub>\<S>\<^sup>\<int> i2"  using int_1_th_5[of i1 i3,simplified] by ty_auto
                   also have "...= i1 +\<^sub>\<S>\<^sup>\<int> (i3 +\<^sub>\<S>\<^sup>\<int> i2)"  using int_1_th_7 F2 by ty_auto                 
                  also have "...= i1 +\<^sub>\<S>\<^sup>\<int> (i2 +\<^sub>\<S>\<^sup>\<int> i3)" using int_1_th_5 by ty_auto
                  finally show ?thesis by auto
          next
            case False
              then show ?thesis using int_1_th_8[of i1 i3 i2] F2 by ty_auto
           qed
     qed
   next
     case F1: False
     show ?thesis  
     proof(cases "i2 is Nat")
       case T2[ty]:True 
         show ?thesis  
         proof(cases "i3 is Nat")
           case T3[ty]:True
           have "(i1 +\<^sub>\<S>\<^sup>\<int> i2) +\<^sub>\<S>\<^sup>\<int> i3 = i3 +\<^sub>\<S>\<^sup>\<int> (i2 +\<^sub>\<S>\<^sup>\<int> i1)" using int_1_th_5 by ty_auto
           also have "... = (i3+\<^sub>\<S>\<^sup>\<int> i2) +\<^sub>\<S>\<^sup>\<int> i1" using int_1_th_7[of i2 i3 i1,simplified] F1 by ty_auto
           finally show ?thesis using int_1_th_5 F1 by ty_auto
         next
           case F3:False
           have  "(i1 +\<^sub>\<S>\<^sup>\<int> i2) +\<^sub>\<S>\<^sup>\<int> i3 = (i2 +\<^sub>\<S>\<^sup>\<int> i1) +\<^sub>\<S>\<^sup>\<int> i3" using int_1_th_5 by ty_auto
           also have "... = i2 +\<^sub>\<S>\<^sup>\<int> (i1 +\<^sub>\<S>\<^sup>\<int> i3)" using int_1_th_8[of i2 i3 i1] F1 F3 by ty_auto
           also have "... = i2 +\<^sub>\<S>\<^sup>\<int> (i3 +\<^sub>\<S>\<^sup>\<int> i1)" using int_1_th_5[of i1 i3] F1 F3 by ty_auto
           also have "... = (i2 +\<^sub>\<S>\<^sup>\<int> i3) +\<^sub>\<S>\<^sup>\<int> i1" using int_1_th_8[of i2 i1 i3] F1 F3 by ty_auto
           finally show ?thesis using int_1_th_5[of i1] by ty_auto
         qed
       next
         case F2:False
         show ?thesis  
         proof(cases "i3 is Nat")
           case T3[ty]:True
                   have  "(i1 +\<^sub>\<S>\<^sup>\<int> i2) +\<^sub>\<S>\<^sup>\<int> i3 = i3 +\<^sub>\<S>\<^sup>\<int> (i2 +\<^sub>\<S>\<^sup>\<int> i1)" using int_1_th_5 by ty_auto
                   also have  "... = (i3 +\<^sub>\<S>\<^sup>\<int> i2) +\<^sub>\<S>\<^sup>\<int> i1" using int_1_th_8[of i3] F1 F2 by ty_auto
                   also have  "... = i1 +\<^sub>\<S>\<^sup>\<int> (i2 +\<^sub>\<S>\<^sup>\<int> i3)" using int_1_th_5 by ty_auto
                   finally show ?thesis by auto         
           next case F3: False
                         then obtain k3 where [ty]: "k3 be Nat" and
                          A3: "k3<>{} & i3=[{},k3]" using int_1_th_1[of i3] by ty_auto
                         obtain k2 where [ty]: "k2 be Nat" and
                          A2: "k2<>{} & i2=[{},k2]" using int_1_th_1[of i2] F2 by ty_auto
                         obtain k1 where [ty]: "k1 be Nat" and
                          A1: "k1<>{} & i1=[{},k1]" using int_1_th_1[of i1] F1 by ty_auto
                         have "k1 +\<^sub>\<S>\<^sup>\<nat> k2 <>{}" "k2 +\<^sub>\<S>\<^sup>\<nat> k3 <>{}" 
                           using A1 A2 A3 Add_14[of k2 k1] Add_14[of k3 k2] by ty_auto
                         hence [ty]:"[{},(k1 +\<^sub>\<S>\<^sup>\<nat> k2)] is Integer" "[{},(k2 +\<^sub>\<S>\<^sup>\<nat> k3)] is Integer" using pair_int by infer_auto
                         have H1: "i1 +\<^sub>\<S>\<^sup>\<int> i2 = [{},(k1 +\<^sub>\<S>\<^sup>\<nat> k2)]" using int_1_def_3[of i1 i2,simplified] A1 A2 F1 F2 by infer_auto
                         have H2: "i2 +\<^sub>\<S>\<^sup>\<int> i3 = [{},(k2 +\<^sub>\<S>\<^sup>\<nat> k3)]" using int_1_def_3[of i2 i3,simplified] A3 A2 F3 F2 by infer_auto
                         have "(i1 +\<^sub>\<S>\<^sup>\<int> i2) +\<^sub>\<S>\<^sup>\<int> i3 = [{},((k1 +\<^sub>\<S>\<^sup>\<nat> k2)+\<^sub>\<S>\<^sup>\<nat> k3)]"
                           using int_1_def_3[of "[{},(k1 +\<^sub>\<S>\<^sup>\<nat> k2)]" i3,simplified] A3 F3 H1 by infer_auto
                         also have "\<dots>= [{},(k1 +\<^sub>\<S>\<^sup>\<nat> (k2+\<^sub>\<S>\<^sup>\<nat> k3))]" using Add_7 by ty_auto
                         also have "\<dots>=i1 +\<^sub>\<S>\<^sup>\<int> (i2 +\<^sub>\<S>\<^sup>\<int> i3)"
                           using int_1_def_3[of i1 "[{},(k2 +\<^sub>\<S>\<^sup>\<nat> k3)]",simplified] A1 F1 H2 by infer_auto
                         finally show ?thesis by auto  
    qed                                 
  qed
qed

mtheorem int_1_th_10:
  "i1 +\<^sub>\<S>\<^sup>\<int> i2 = i1 +\<^sub>\<S>\<^sup>\<int> i3 implies i2 = i3"
proof(standard, cases "i1 is Nat")
  assume A0: "i1 +\<^sub>\<S>\<^sup>\<int> i2 = i1 +\<^sub>\<S>\<^sup>\<int> i3"
  case [ty]: True
    show "i2 = i3"
    proof(cases "i2 is Nat")
      case [ty]: True
        hence A1: "i1 +\<^sub>\<S>\<^sup>\<int> i2 = i1 +\<^sub>\<S>\<^sup>\<nat> i2" using int_1_def_3 by ty_auto
        show ?thesis
        proof(cases "i3 is Nat")
          case [ty]: True
          hence "i1 +\<^sub>\<S>\<^sup>\<int> i3 = i1 +\<^sub>\<S>\<^sup>\<nat> i3" using int_1_def_3 by ty_auto
          thus ?thesis using A0 A1 Add_11[of i3 i2 i1] by ty_auto
        next
          case False
          then obtain k3 where [ty]: "k3 be Nat" and
             B1: "k3<>{} & i3=[{},k3]" using int_1_th_1[of i3] by ty_auto  
          hence B2: "i1 +\<^sub>\<S>\<^sup>\<nat> i2 = i1 -- k3" 
            using A0 A1 int_1_def_3[of i1 i3,simplified] by infer_auto
          have "(i1 +\<^sub>\<S>\<^sup>\<nat> i2) is Nat" by infer_auto
          hence [ty]: "i1 -- k3 is Nat" using B2 by ty_auto
          hence "k3 c= i1" using int_0_th_4[of k3 i1,simplified] by ty_auto
          hence "(i1 -- k3) +\<^sub>\<S>\<^sup>\<nat> k3 = i1" using int_0_def_1[of i1 k3,simplified] by ty_auto 
          hence "i1 +\<^sub>\<S>\<^sup>\<nat> (i2 +\<^sub>\<S>\<^sup>\<nat> k3) = i1 +\<^sub>\<S>\<^sup>\<nat> {}" using B2 Add_7[of k3 i2 i1] Add_3 by ty_auto
          hence "i2 +\<^sub>\<S>\<^sup>\<nat> k3 = {}" using Add_11[of  "{}" _ i1] by infer_auto
          thus ?thesis using B1 Add_14[of k3 i2] by ty_auto
        qed
      next case False
        then obtain k2 where [ty]: "k2 be Nat" and
          C1: "k2<>{} & i2=[{},k2]" using int_1_th_1[of i2] by ty_auto  
        have C2: "i1 +\<^sub>\<S>\<^sup>\<int> i2 = i1 -- k2" 
          using C1 int_1_def_3[of i1 i2,simplified] by infer_auto
        show ?thesis
          proof(cases "i3 is Nat")
            case [ty]: True
              have B2: "i1 +\<^sub>\<S>\<^sup>\<nat> i3 = i1 -- k2" 
                using A0 C1 C2 int_1_def_3[of i1 i3,simplified] by ty_auto
              have "(i1 +\<^sub>\<S>\<^sup>\<nat> i3) is Nat" by infer_auto
              hence [ty]: "i1 -- k2 is Nat" using B2 by ty_auto
              hence "k2 c= i1" using int_0_th_4[of k2 i1,simplified] by ty_auto
              hence "(i1 -- k2) +\<^sub>\<S>\<^sup>\<nat> k2 = i1" using int_0_def_1[of i1 k2,simplified] by ty_auto 
              hence "i1 +\<^sub>\<S>\<^sup>\<nat> (i3 +\<^sub>\<S>\<^sup>\<nat> k2) = i1 +\<^sub>\<S>\<^sup>\<nat> {}" using B2 Add_7[of k2 i3 i1] Add_3 by ty_auto
              hence "i3 +\<^sub>\<S>\<^sup>\<nat> k2 = {}" using Add_11[of  "{}" _ i1] by infer_auto
              thus ?thesis using C1 Add_14[of k2 i3] by ty_auto
            next case False
               then obtain k3 where [ty]: "k3 be Nat" and
                D1: "k3<>{} & i3=[{},k3]" using int_1_th_1[of i3] by ty_auto  
               have "i1 +\<^sub>\<S>\<^sup>\<int> i3 = i1 -- k3" using D1 int_1_def_3[of i1 i3,simplified] by infer_auto
               hence "k2=k3"  using A0 C2 int_0_th_5[of k3 k2 i1] by ty_auto
               then show "i2 = i3" using C1 D1 by simp
        qed
    qed
  next
    assume A0: "i1 +\<^sub>\<S>\<^sup>\<int> i2 = i1 +\<^sub>\<S>\<^sup>\<int> i3"
    case F0: False
      then obtain k1 where [ty]: "k1 be Nat" and
          F1: "k1<>{} & i1=[{},k1]" using int_1_th_1[of i1] by ty_auto       
    show "i2 = i3"
    proof(cases "i2 is Nat")
      case [ty]: True
        hence A1: "i1 +\<^sub>\<S>\<^sup>\<int> i2 = i2 -- k1" using int_1_def_3[of i1 i2,simplified] F0 F1 by infer_auto
        show ?thesis
        proof(cases "i3 is Nat")
          case [ty]: True
          hence A2: "i1 +\<^sub>\<S>\<^sup>\<int> i3 = i3 -- k1" using int_1_def_3[of i1 i3,simplified] F0 F1  by infer_auto 
          hence A3: "i2 --k1 = i3--k1" using A0 A1 by auto 
          show "i2 = i3"
          proof(cases "k1 c= i2")
            case T1: True
              hence [ty]: "i2--k1 is Nat" "i3--k1 is Nat" using A3 int_0_th_4[of k1 i2,simplified] by ty_auto
              hence T2: "k1 c= i3" using int_0_th_4[of k1 i3,simplified] by ty_auto
              hence T3: "(i2--k1) +\<^sub>\<S>\<^sup>\<nat> k1 = i2" "(i3--k1) +\<^sub>\<S>\<^sup>\<nat> k1 = i3" using int_0_def_1 T1 by ty_auto
              have "(i3--k1) +\<^sub>\<S>\<^sup>\<nat> k1 = i2" using A3 T3(1) by simp 
              then show ?thesis using T3(2) by simp 
            next
              case F2:False
                hence [ty]: "not i2--k1 is Nat" "not i3--k1 is Nat" using A3 int_0_th_4[of k1 i2,simplified] by ty_auto    
                hence F3:"not k1 c= i3" using int_0_th_4[of k1 i3,simplified] by ty_auto
                have "i2 in k1" using F2 ordinal1_th_12[of i2 k1] by ty_auto
                then obtain j2 where [ty]:"j2 is Nat" and
                  F4: "j2 <>{} & i2+\<^sub>\<S>\<^sup>\<nat> j2 = k1" using Add_8 by ty_auto
                have "i3 in k1" using F3 ordinal1_th_12[of i3 k1] by ty_auto
                then obtain j3 where [ty]: "j3 is Nat" and
                  F5: "j3 <>{} & i3+\<^sub>\<S>\<^sup>\<nat> j3 = k1" using Add_8 by ty_auto
                have "i2--k1 = [{},j2]" "i3--k1 = [{},j3]" using int_0_th_3 F4 F5 by ty_auto
                hence "[{},j2] = [{},j3]" using A3 by auto
                hence "j2 =j3" using xtuple_0_th_1a by auto
                hence "j2+\<^sub>\<S>\<^sup>\<nat> i2 = j2 +\<^sub>\<S>\<^sup>\<nat> i3" using F4 F5 Add_6 by ty_auto
                then show "i2 = i3" using F4 F5 Add_11[of i3 i2 j2] by ty_auto 
          qed
        next case F3: False
          then obtain k3 where [ty]: "k3 be Nat" and
          C1: "k3<>{} & i3=[{},k3]" using int_1_th_1[of i3] by ty_auto  
          have C2: "i1 +\<^sub>\<S>\<^sup>\<int> i3 = [{}, (k1+\<^sub>\<S>\<^sup>\<nat> k3)]" using int_1_def_3[of i1 i3,simplified] F1 C1 by infer_auto
          hence "not i1+\<^sub>\<S>\<^sup>\<int> i3 is Nat" by infer_auto
          hence "not i2 -- k1 is Nat" using A1 A0 by ty_auto 
          hence " not k1 c= i2" using int_0_th_4 A1 A0 by ty_auto
          hence "i2 in k1" using ordinal1_th_12[of i2 k1] by ty_auto
          then obtain k2 where [ty]: "k2 be Nat" and
            C3: "k2 <>{} & i2 +\<^sub>\<S>\<^sup>\<nat> k2 =k1" using Add_8 by ty_auto
          hence "i2 -- k1 = [{},k2]" using int_0_th_3[of k1 k2 i2] by ty_auto
          hence "k2 = (k1+\<^sub>\<S>\<^sup>\<nat> k3)" using C2 A0 A1 xtuple_0_th_1a by auto
          hence "k2 +\<^sub>\<S>\<^sup>\<nat> {} = k2 +\<^sub>\<S>\<^sup>\<nat> (i2+\<^sub>\<S>\<^sup>\<nat> k3)" using C3 Add_6[of k2 i2,simplified] Add_7[of k3 i2 k2,simplified] 
           Add_3[of k2,simplified] by infer_auto
          with Add_11[of "i2 +\<^sub>\<S>\<^sup>\<nat> k3" "{}" k2] have "{} = (i2+\<^sub>\<S>\<^sup>\<nat> k3)" by inst_pass_auto
          thus ?thesis using Add_14[of k3 i2] C1 by ty_auto
        qed
      next
        case F2:False
          then obtain k2 where [ty]: "k2 be Nat" and
          C1: "k2<>{} & i2=[{},k2]" using int_1_th_1[of i2] by ty_auto  
          have C2: "i1 +\<^sub>\<S>\<^sup>\<int> i2 = [{}, (k1+\<^sub>\<S>\<^sup>\<nat> k2)]" using int_1_def_3[of i1 i2,simplified] F1 C1 by infer_auto
         show ?thesis
         proof(cases "i3 is Nat")
           case [ty]: True
             hence A1: "i1 +\<^sub>\<S>\<^sup>\<int> i3 = i3 -- k1" using int_1_def_3[of i1 i3,simplified] F0 F1 by infer_auto
             have "not i1+\<^sub>\<S>\<^sup>\<int> i2 is Nat" using C2 by infer_auto
             hence "not i3 -- k1 is Nat" using A1 A0 by ty_auto 
             hence " not k1 c= i3" using int_0_th_4 A1 A0 by ty_auto
             hence "i3 in k1" using ordinal1_th_12[of i3 k1] by ty_auto
             then obtain k3 where [ty]: "k3 be Nat" and
             C3: "k3 <>{} & i3 +\<^sub>\<S>\<^sup>\<nat> k3 =k1" using Add_8 by ty_auto
             hence "i3 -- k1 = [{},k3]" using int_0_th_3[of k1 k3 i3] by ty_auto
             hence "k3 = (k1+\<^sub>\<S>\<^sup>\<nat> k2)" using C2 A0 A1 xtuple_0_th_1a by auto
             hence "k3 +\<^sub>\<S>\<^sup>\<nat> {} = k3 +\<^sub>\<S>\<^sup>\<nat> (i3+\<^sub>\<S>\<^sup>\<nat> k2)" using C3 Add_6[of k3 i3,simplified] Add_7[of k2 i3 k3,simplified] 
               Add_3[of k3,simplified] by infer_auto
             with Add_11[of "i3 +\<^sub>\<S>\<^sup>\<nat> k2" "{}" k3] have "{} = (i3+\<^sub>\<S>\<^sup>\<nat> k2)" by inst_pass_auto
             thus ?thesis using Add_14[of k2 i3] C1 by ty_auto
         next
           case F3:False
             then obtain k3 where [ty]: "k3 be Nat" and
             D1: "k3<>{} & i3=[{},k3]" using int_1_th_1[of i3] by ty_auto  
             have D2: "i1 +\<^sub>\<S>\<^sup>\<int> i3 = [{}, (k1+\<^sub>\<S>\<^sup>\<nat> k3)]" using int_1_def_3[of i1 i3,simplified] F1 D1 by infer_auto
             hence "k1 +\<^sub>\<S>\<^sup>\<nat> k2 = k1 +\<^sub>\<S>\<^sup>\<nat> k3" using A0 C2 xtuple_0_th_1a by auto
             hence "k2 = k3" using Add_11[of k3 k2 k1] by ty_auto
             thus ?thesis using D1 C1 by auto
        qed
     qed
   qed    


mdef int_1_def_4 ( "-\<^sub>\<S>\<^sup>\<H> _" 110) where
  mlet "i be Integer"
  "func -\<^sub>\<S>\<^sup>\<H> i  \<rightarrow> Integer means
     \<lambda>it . it +\<^sub>\<S>\<^sup>\<int> i = {}"
proof-
  show "ex x be Integer st  x +\<^sub>\<S>\<^sup>\<int> i = {}"
  proof(cases "i ={}")
    case True
    thus ?thesis using bexI[of _ "{}" Integer] int_1_th_2[of "{}"] by ty_auto
  next case F: False
    show ?thesis 
    proof(cases "i is Nat")
      case [ty]: True
        hence [ty]: "[{},i] is Integer" using pair_int F by auto
        thus ?thesis using bexI[of _ "[{},i]" Integer] int_1_th_3[of i] F by ty_auto
      next case False
        then obtain k where [ty]: "k be Nat"  and 
          A1:"k\<noteq>{} & i = [{},k]" using int_1_th_1[of i] by ty_auto
       thus ?thesis using bexI[of _ "k" Integer] int_1_th_3[of k] F by ty_auto
    qed
  qed
  fix i1 i2 assume [ty]: "i1 is Integer" "i2 is Integer" and
  A1:"i1 +\<^sub>\<S>\<^sup>\<int> i = {}" "i2 +\<^sub>\<S>\<^sup>\<int> i = {}"
  have "i1 = i1 +\<^sub>\<S>\<^sup>\<int> (i +\<^sub>\<S>\<^sup>\<int> i2)" using  A1 int_1_th_2 int_1_th_5 by ty_auto
  hence "i1 =  (i1 +\<^sub>\<S>\<^sup>\<int> i) +\<^sub>\<S>\<^sup>\<int> i2" using int_1_th_9 by ty_auto
  then show "i1 = i2" using int_1_th_2[of i2] A1(1) by ty_auto
qed mauto

mtheorem int_1_th_11:
  "k<>{} implies (-\<^sub>\<S>\<^sup>\<H> k) = [{},k] & (-\<^sub>\<S>\<^sup>\<H> [{},k]) = k"
proof(intro impI conjI)
  assume K: "k<>{}"
  hence [ty]: "[{},k] is Integer" using pair_int by ty_auto
  have A1: "[{},k] +\<^sub>\<S>\<^sup>\<int> k = {}" "k +\<^sub>\<S>\<^sup>\<int> [{},k] = {}" using K int_1_th_3 by ty_auto
  then show "(-\<^sub>\<S>\<^sup>\<H> k) = [{},k]" "(-\<^sub>\<S>\<^sup>\<H> [{},k]) = k "using int_1_def_4_uniq[of k "[{},k]"] 
    int_1_def_4_uniq[of "[{},k]" k] by ty_auto  
qed

mtheorem int_1_th_12:
 "-\<^sub>\<S>\<^sup>\<H> {} = {}"
proof-
  have "{} +\<^sub>\<S>\<^sup>\<int> {} = {}" using int_1_th_2 by ty_auto
  then show "-\<^sub>\<S>\<^sup>\<H> {} = {}" using int_1_def_4_uniq[of "{}" "{}"] by ty_auto  
qed

mtheorem int_1_th_13:
 "-\<^sub>\<S>\<^sup>\<H> (-\<^sub>\<S>\<^sup>\<H> i) = i"
proof(cases "not i is Nat")
  case True
    then obtain k where [ty]:"k be Nat" and
       A1: "k<>{} & i = [{},k]" using int_1_th_1[of i] by ty_auto 
    then show "-\<^sub>\<S>\<^sup>\<H> (-\<^sub>\<S>\<^sup>\<H> i) = i" using int_1_th_11[of k] by auto
  next
    case [ty]: False
    show "-\<^sub>\<S>\<^sup>\<H> (-\<^sub>\<S>\<^sup>\<H> i) = i"
    proof(cases "i={}")
      case True 
      thus ?thesis using int_1_th_12 by auto
    next
      case False 
         then show "-\<^sub>\<S>\<^sup>\<H> (-\<^sub>\<S>\<^sup>\<H> i) = i" using int_1_th_11[of i] by ty_auto
    qed
qed
  
mtheorem
  mlet "i be non natural\<bar>Integer"
  "cluster  -\<^sub>\<S>\<^sup>\<H> i \<rightarrow> natural"
proof
  obtain k where [ty]: "k be Nat" and
    A1: "k<>{} & i = [{},k]" using int_1_th_1[of i] by ty_auto
  hence "(-\<^sub>\<S>\<^sup>\<H> [{},k]) = k" using int_1_th_11 by auto
  then show "-\<^sub>\<S>\<^sup>\<H> i is natural" using A1 by ty_auto 
qed

mdef int_1_def_5 ("_ *\<^sub>\<S>\<^sup>\<int> _" [100,101] 100) where
  mlet "i be Integer","j be Integer"
  "func i *\<^sub>\<S>\<^sup>\<int> j \<rightarrow> Integer means
      \<lambda>it . (i *\<^sub>\<S>\<^sup>\<nat> j) = it  if i is natural & j is natural,  
      \<lambda>it . -\<^sub>\<S>\<^sup>\<H> ((-\<^sub>\<S>\<^sup>\<H> i) *\<^sub>\<S>\<^sup>\<nat> j) = it  if not i is natural & j is natural,
      \<lambda>it . -\<^sub>\<S>\<^sup>\<H> (i *\<^sub>\<S>\<^sup>\<nat> (-\<^sub>\<S>\<^sup>\<H> j)) = it if i is natural & not j is natural otherwise
      \<lambda>it . (-\<^sub>\<S>\<^sup>\<H> i) *\<^sub>\<S>\<^sup>\<nat> (-\<^sub>\<S>\<^sup>\<H> j) =it "
proof-
  show "(i be natural \<and> j be natural \<longrightarrow> (\<exists>x : Integer. (i *\<^sub>\<S>\<^sup>\<nat> j) = x)) \<and>
    (\<not> i be natural \<and> j be natural \<longrightarrow> (\<exists>x : Integer. -\<^sub>\<S>\<^sup>\<H> ((-\<^sub>\<S>\<^sup>\<H> i) *\<^sub>\<S>\<^sup>\<nat> j) = x)) \<and>
    (i be natural \<and> \<not> j be natural \<longrightarrow> (\<exists>x : Integer. -\<^sub>\<S>\<^sup>\<H> (i *\<^sub>\<S>\<^sup>\<nat> (-\<^sub>\<S>\<^sup>\<H> j)) = x)) \<and>
    (\<not> (i be natural \<and> j be natural) \<and> \<not> (\<not> i be natural \<and> j be natural) 
\<and> \<not> (i be natural \<and> \<not> j be natural) \<longrightarrow> (\<exists>x : Integer. (-\<^sub>\<S>\<^sup>\<H> i) *\<^sub>\<S>\<^sup>\<nat> (-\<^sub>\<S>\<^sup>\<H> j) = x))"
  proof(intro impI conjI)
    assume [ty]: "i be natural \<and> j be natural"
    show "\<exists>x : Integer. i *\<^sub>\<S>\<^sup>\<nat> j = x" using bexI[of _ "i *\<^sub>\<S>\<^sup>\<nat> j" Integer] by infer_auto
  next
    assume [ty]: "\<not> i be natural \<and> j be natural"
    show "\<exists>x : Integer. -\<^sub>\<S>\<^sup>\<H> ((-\<^sub>\<S>\<^sup>\<H> i) *\<^sub>\<S>\<^sup>\<nat> j) = x" using bexI[of _ "-\<^sub>\<S>\<^sup>\<H> ((-\<^sub>\<S>\<^sup>\<H> i) *\<^sub>\<S>\<^sup>\<nat> j)" Integer ] by infer_auto
  next
    assume [ty]: " i be natural \<and> \<not> j be natural"
    show "\<exists>x : Integer. -\<^sub>\<S>\<^sup>\<H> (i *\<^sub>\<S>\<^sup>\<nat> (-\<^sub>\<S>\<^sup>\<H> j)) = x" using bexI[of _ "-\<^sub>\<S>\<^sup>\<H> (i *\<^sub>\<S>\<^sup>\<nat> (-\<^sub>\<S>\<^sup>\<H> j))" Integer ] by infer_auto
  next 
    assume "\<not> (i be natural \<and> j be natural) \<and> \<not> (\<not> i be natural \<and> j be natural) \<and> \<not> (i be natural \<and> \<not> j be natural)"
    hence [ty]: "\<not> i be natural \<and> \<not> j be natural" by auto
     show "\<exists>x : Integer. (-\<^sub>\<S>\<^sup>\<H> i) *\<^sub>\<S>\<^sup>\<nat> (-\<^sub>\<S>\<^sup>\<H> j) = x" using bexI[of _ "(-\<^sub>\<S>\<^sup>\<H> i) *\<^sub>\<S>\<^sup>\<nat> (-\<^sub>\<S>\<^sup>\<H> j)" Integer] by infer_auto
   qed
   fix x y assume [ty]: "x be Integer" "y be Integer"
   show "((i be natural \<and> j be natural) \<and> (i *\<^sub>\<S>\<^sup>\<nat> j) = x \<and> (i *\<^sub>\<S>\<^sup>\<nat> j) = y \<longrightarrow> x = y) \<and>
               ((\<not> i be natural \<and> j be natural) \<and> (-\<^sub>\<S>\<^sup>\<H> ((-\<^sub>\<S>\<^sup>\<H> i) *\<^sub>\<S>\<^sup>\<nat> j)) = x \<and> (-\<^sub>\<S>\<^sup>\<H> ((-\<^sub>\<S>\<^sup>\<H> i) *\<^sub>\<S>\<^sup>\<nat> j)) = y \<longrightarrow> x = y) \<and>
           ((i be natural \<and> \<not> j be natural) \<and> (-\<^sub>\<S>\<^sup>\<H> (i *\<^sub>\<S>\<^sup>\<nat> (-\<^sub>\<S>\<^sup>\<H> j))) = x \<and> (-\<^sub>\<S>\<^sup>\<H> (i *\<^sub>\<S>\<^sup>\<nat> (-\<^sub>\<S>\<^sup>\<H> j))) = y \<longrightarrow> x = y) \<and>
           (\<not> (i be natural \<and> j be natural) \<and>
            \<not> (\<not> i be natural \<and> j be natural) \<and> \<not> (i be natural \<and> \<not> j be natural) \<and> ((-\<^sub>\<S>\<^sup>\<H> i) *\<^sub>\<S>\<^sup>\<nat> (-\<^sub>\<S>\<^sup>\<H> j)) = x \<and> ((-\<^sub>\<S>\<^sup>\<H> i) *\<^sub>\<S>\<^sup>\<nat> (-\<^sub>\<S>\<^sup>\<H> j)) = y \<longrightarrow>
            x = y)" by blast
 qed mauto  

end

