theory binop_1
imports funct_2
begin


mdef binop_0_def_1 (" _ . \<lparr> _ , _ \<rparr>"[90,90,90]) where
  mlet "f be Function", "a be object", "b be object"
  "func f . \<lparr> a , b \<rparr> \<rightarrow> set equals f.[a,b]"
proof -
  show "(f.[a,b]) be set" using all_set by simp
qed

mtheorem binop_0_def_2:
 mlet "A be non empty \<bar> set",
" B be non empty \<bar> set","C be set","
        f be (Function-of [:A,B:],C)"," a be (Element-of A)"," b be (Element-of B)"
  "redefine func f.\<lparr>a,b\<rparr>  \<rightarrow> Element-of C"
proof
  have "a in A" "b in B " using subset_1_def_1[of A a] subset_1_def_1[of B b] by ty_auto
  hence "[a,b] in [:A,B:]" using zfmisc_1_def_2 by ty_auto
  hence "[:A,B:] be non empty\<bar>set" "[a,b] be Element-of [:A,B:]" using Element(6) xboole_0_def_1 by ty_auto
  hence "(f.[a,b]) be Element-of C" using funct_2_def_5[of "[:A,B:]" "C" "f" "[a,b]"]  by mauto
  thus "f.\<lparr> a, b \<rparr> be Element-of C" using binop_0_def_1 by mauto
qed

abbreviation (input) binop_1_mode_1 ("UnOp-of _" [190] 190) where
  "UnOp-of X \<equiv> Function-of X , X"

abbreviation binop_1_mode_2 ("BinOp-of _" [190] 190) where
  "BinOp-of X \<equiv> Function-of [:X,X:] , X"

mtheorem binop_1_mode_2:
  "x be BinOp-of X \<Longrightarrow> dom x = [:X,X:]"
proof-
  assume [ty]:"x be BinOp-of X"
  show "dom x = [:X,X:]"
 proof(cases "X={}")
      assume A1: "X={}"
       hence "x = {}" using funct_2_def_1E[of "[:X,X:]" X x] by mauto
       hence A2: "dom x={}" using empty1[of "dom {}"] by mauto
       have "not not[:X,X:] = {}"
       proof
         assume "[:X,X:] \<noteq> {}"
         hence "[:X,X:] is non empty" using xboole_0_lm_1 by ty_auto
         then obtain x where
           "x in [:X,X:]" using xboole_0_def_1 by ty_auto
         then obtain y z where
           "x=[y,z]" "y in X & z in X" using zfmisc_1_def_2 by ty_auto
         then show "False" using A1 xb by auto
       qed
       thus ?thesis using A2 by auto
     next
        assume A2: "X\<noteq>{}"
       hence "X is non empty" using xboole_0_lm_1[of X,simplified] by ty_auto
       then show "dom x = [:X,X:]" using A2 funct_2_def_1E[of "[:X,X:]" X x] by mauto
     qed   
qed

mtheorem binop_0_def_20A:
  mlet "A be set", "f be BinOp-of A", "a be Element-of A", "b be Element-of A"
  "redefine func f.\<lparr>a,b\<rparr> \<rightarrow> Element-of A"
proof
  have Z: "f.\<lparr> a,b \<rparr> = f.[a,b]" using binop_0_def_1 by mauto
  show "f.\<lparr>a,b\<rparr> be (Element-of A)"
    proof(cases "A={}")
      assume A1: "A={}"
       hence "f = {}" using funct_2_def_1E[of "[:A,A:]" A f] by mauto
       hence "not [a,b] in dom f" using empty1[of "dom {}"] xb by mauto
       hence "f.[a,b] = {}" using funct_1_def_2 by mauto
      thus "f.\<lparr>a,b\<rparr> be (Element-of A)" using A1 Z Element(3) by simp
    next
      assume A2: "A\<noteq>{}"
       hence "A is non empty" using xboole_0_lm_1[of A,simplified] by ty_auto
       hence "dom f = [:A,A:]" "a in A" "b in A" using A2 funct_2_def_1E[of "[:A,A:]" A f] Element_of_rule2 by mauto
       hence "[a,b] in [:A,A:]" using zfmisc_1_def_2 by ty_auto
       hence "[:A,A:] be non empty\<bar>set" "[a,b] be Element-of [:A,A:]" using Element(6) xboole_0_def_1 by ty_auto
       hence "(f.[a,b]) be Element-of A"
         by (intro funct_2_def_5) mauto
      thus "f.\<lparr>a,b\<rparr> be (Element-of A)" using Z by auto
    qed
  qed
    
notation (input) xboole_0K1 ("op0")

mtheorem
  "cluster op0 \<rightarrow> set" by mauto

abbreviation funct_5_def_6 ("op2") where
  "op2 \<equiv>{[ op0,op0 ,op0]}"

mtheorem 
  "cluster op2 \<rightarrow> set" by mauto

mtheorem 
  "cluster op0 \<rightarrow> Element-of {{}}" using tarski_def_1 Element(6) by mauto
  
mtheorem
  "cluster op2 \<rightarrow> BinOp-of {{}}"
proof
  have B1: "op2 be Function" by mauto
  hence "dom op2=[:{{}},{{}}:]" "rng op2 = {{}}" using
              relat_1_th_3[of "{}" "[{},{}]" op2] zfmisc_1_th_28 by auto
  thus B2: "op2 be BinOp-of {{}}" using funct_2_th_2[of op2,OF B1] by auto
qed

abbreviation funct_5_def_x ("op1") where
  "op1 \<equiv>{[ op0,op0]}"

mtheorem 
  "cluster op1 \<rightarrow> set"  by mauto
   
   
   
mtheorem 
  "cluster op1 \<rightarrow> Function-of {{}},{{}}"
proof
  have B1: "op1 be Function" by mauto
  hence "dom op1={{}}" "rng op1 = {{}}" using
              relat_1_th_3[of "{}" "{}" op1] zfmisc_1_th_28 by auto
  thus B2: "op1 be Function-of {{}},{{}}" using funct_2_th_2[of op1,OF B1] by auto
qed

mtheorem 
mlet "a be object", "c be object"
  "cluster (a .\<midarrow>> c) \<rightarrow> Function-of {a} , {c}"
proof
  let ?ac="a .\<midarrow>> c"
  have A1: "[:{a},{c}:] = {[a,c]}" using zfmisc_1_th_28 by auto
  have A2: "?ac = [:{a},{c}:]" using funcop_1_def_9 funcop_1_def_2 by mauto

  have [ty]: "?ac be Function" by mauto
  have "dom ?ac={a}" "rng ?ac = {c}" using
              relat_1_th_3[of "c" a ?ac] A1 A2 zfmisc_1_th_28 by mauto
  thus B2: "?ac be Function-of {a} , {c}" using funct_2_th_2 by mauto

qed


mtheorem 
  mlet "a be object", "b be object", "c be object"
  "cluster [a,b] .\<midarrow>> c \<rightarrow> Function-of [:{a},{b}:] , {c}"
proof
  let ?abc="[a,b] .\<midarrow>> c"
  have A1: "[:{[a,b]},{c}:] = {[a,b,c]}" using zfmisc_1_th_28 by auto
  have A2: "?abc = [:{[a,b]},{c}:]" using funcop_1_def_9[of "[a , b]" ] funcop_1_def_2 by mauto

  have [ty]: "?abc be Function" by mauto
  have "dom ?abc=[:{a},{b}:]" "rng ?abc = {c}" using
              relat_1_th_3[of "c" "[a,b]" ?abc] A1 A2 zfmisc_1_th_28 by mauto
  thus B2: "?abc be Function-of [:{a},{b}:] , {c}" using funct_2_th_2 by mauto
qed

end
