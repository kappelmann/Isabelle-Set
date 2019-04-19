theory binop_2
  imports int_1 binop_1
begin

reserve i1, i2 for Integer

mdef binop_2_def_20 ("addint") where
  "func addint \<rightarrow> BinOp-of INT means
      \<lambda>it . for i1,i2 holds it.\<lparr> i1,i2 \<rparr> = i1 +\<^sub>\<S>\<^sup>\<int> i2"
proof-
  let ?F = "\<lambda> x . (x`1) +\<^sub>\<S>\<^sup>\<int> (x`2)"
  have P1: "INT is non empty\<bar>set" by ty_auto
  hence P2: "[:INT,INT:] is non empty\<bar>set" by ty_auto
  have P3: "\<forall>x:Element-of [:INT,INT:]. ?F(x) be Element-of INT"
  proof
    fix x assume "x is Element-of [:INT,INT:]"
    hence "x in [:INT,INT:]" using Element(7) by ty_auto  
    then obtain a b where 
      X1: "x=[a,b] & a in INT & b in INT" using zfmisc_1_def_2 by ty_auto
    have [ty]: "a is Integer" "b is Integer" using int_1_def_2 X1 by auto 
    have "x`1 = a" "x`2 = b" using xtuple_0_reduce[of a b] X1 by auto
    hence "?F(x) in INT" using X1 int_1_def_2[of "a +\<^sub>\<S>\<^sup>\<int> b"] by infer_auto
    then show "?F(x) be Element-of INT" using Element(6) by ty_auto
  qed mauto
  obtain f where [ty]:"f be Function-of [:INT,INT:],INT"
    and  A1: "for x be Element-of [:INT,INT:] holds (f. x) =  ?F(x)" using funct_2_sch_4[OF P2 P1 P3] by auto
  have [ty]:"f is Function" by ty_auto
  show "ex f be BinOp-of INT st  \<forall>i1 : Integer. \<forall>i2 : Integer.  f . \<lparr> i1 , i2 \<rparr> = i1 +\<^sub>\<S>\<^sup>\<int> i2"
  proof(rule bexI[of _ f],intro ballI)
    fix i1 i2 assume "i1 is Integer" "i2 is Integer"
    hence "[i1,i2] in [:INT,INT:]" using zfmisc_1_th_87 int_1_def_2 by ty_auto
    hence "(f. [i1,i2]) =  ?F([i1,i2])" using A1 Element(6) by ty_auto
    then show "f. \<lparr>i1,i2\<rparr> =  i1 +\<^sub>\<S>\<^sup>\<int> i2" using binop_0_def_1 xtuple_0_reduce[of i1 i2] by ty_auto 
  qed mauto
  fix f1 f2 assume [ty]: "f1 is BinOp-of INT" "f2 is BinOp-of INT"
      and
    A1: "for i1,i2 holds f1.\<lparr> i1,i2 \<rparr> = i1 +\<^sub>\<S>\<^sup>\<int> i2" and
    A2: "for i1,i2 holds f2.\<lparr> i1,i2 \<rparr> = i1 +\<^sub>\<S>\<^sup>\<int> i2"
  have "for a be Element-of [:INT,INT:] holds f1 . a = f2 . a" 
  proof
    fix x assume "x be Element-of [:INT,INT:]"
     hence "x in [:INT,INT:]" using Element(7) by ty_auto
    then obtain a b where 
      X1: "x=[a,b] & a in INT & b in INT" using zfmisc_1_def_2 by ty_auto
    have [ty]: "a is Integer" "b is Integer" using int_1_def_2 X1 by auto 
    have "f1 . x = a +\<^sub>\<S>\<^sup>\<int> b" using  A1 binop_0_def_1 X1 by ty_auto
    then show "f1 .x = f2. x" using  A2 binop_0_def_1 X1 by ty_auto
  qed mauto
  then show "f1=f2" using funct_2_def_7I[of "[:INT,INT:]" INT] by ty_auto 
qed mauto


mdef binop_2_def_22 ("multint") where
  "func multint \<rightarrow> BinOp-of INT means
      \<lambda>it . for i1,i2 holds it.\<lparr> i1,i2 \<rparr> = i1 *\<^sub>\<S>\<^sup>\<int> i2"
proof-
  let ?F = "\<lambda> x . (x`1) *\<^sub>\<S>\<^sup>\<int> (x`2)"
  have P1: "INT is non empty\<bar>set" by ty_auto
  hence P2: "[:INT,INT:] is non empty\<bar>set" by ty_auto
  have P3: "\<forall>x:Element-of [:INT,INT:]. ?F(x) be Element-of INT"
  proof
    fix x assume "x is Element-of [:INT,INT:]"
    hence "x in [:INT,INT:]" using Element(7) by ty_auto
    then obtain a b where 
      X1: "x=[a,b] & a in INT & b in INT" using zfmisc_1_def_2 by ty_auto
    have [ty]: "a is Integer" "b is Integer" using int_1_def_2 X1 by auto 
    have "x`1 = a" "x`2 = b" using xtuple_0_reduce[of a b] X1 by auto
    hence "?F(x) in INT" using X1 int_1_def_2[of "a *\<^sub>\<S>\<^sup>\<int> b"] by infer_auto
    then show "?F(x) be Element-of INT" using Element(6) by ty_auto
  qed mauto
  obtain f where [ty]:"f be Function-of [:INT,INT:],INT"
    and  A1: "for x be Element-of [:INT,INT:] holds (f. x) =  ?F(x)" using funct_2_sch_4[OF P2 P1 P3] by auto
  have [ty]:"f is Function" by ty_auto   
  show "ex f be BinOp-of INT st  \<forall>i1 : Integer. \<forall>i2 : Integer.  f . \<lparr> i1 , i2 \<rparr> = i1 *\<^sub>\<S>\<^sup>\<int> i2"
  proof(rule bexI[of _ f],intro ballI)
    fix i1 i2 assume "i1 is Integer" "i2 is Integer"
    hence "[i1,i2] in [:INT,INT:]" using zfmisc_1_th_87 int_1_def_2 by ty_auto
    hence "(f. [i1,i2]) =  ?F([i1,i2])" using A1 Element(6) by ty_auto
    then show "f. \<lparr>i1,i2\<rparr> =  i1 *\<^sub>\<S>\<^sup>\<int> i2" using binop_0_def_1 xtuple_0_reduce[of i1 i2] by ty_auto 
  qed mauto
  fix f1 f2 assume [ty]: "f1 is BinOp-of INT" "f2 is BinOp-of INT"
      and
    A1: "for i1,i2 holds f1.\<lparr> i1,i2 \<rparr> = i1 *\<^sub>\<S>\<^sup>\<int> i2" and
    A2: "for i1,i2 holds f2.\<lparr> i1,i2 \<rparr> = i1 *\<^sub>\<S>\<^sup>\<int> i2"
  have "for a be Element-of [:INT,INT:] holds f1 . a = f2 . a" 
  proof
    fix x assume "x be Element-of [:INT,INT:]"
     hence "x in [:INT,INT:]" using Element(7) by ty_auto
    then obtain a b where 
      X1: "x=[a,b] & a in INT & b in INT" using zfmisc_1_def_2 by ty_auto
    have [ty]: "a is Integer" "b is Integer" using int_1_def_2 X1 by auto 
    have "f1 . x = a *\<^sub>\<S>\<^sup>\<int> b" using  A1 binop_0_def_1 X1 by ty_auto
    then show "f1 .x = f2. x" using  A2 binop_0_def_1 X1 by ty_auto
  qed mauto
  then show "f1=f2" using funct_2_def_7I[of "[:INT,INT:]" INT] by ty_auto 
qed mauto

end