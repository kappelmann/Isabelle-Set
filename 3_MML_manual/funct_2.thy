theory funct_2
imports partfun_1 funcop_1
begin    

reserve x,y,z,x1,x2,y1,y2 for object
reserve X,Y,Z for set
reserve f,g for Function
  
section "funct_2"
      
mdef funct_2_def_1 ("_ , _ : quasi-total" [110,110] 110) where
   mlet "X be set", "Y be set"
   "attr (X , Y :quasi-total) for (Relation-of X,Y) means
     (\<lambda> IT. X = dom IT) if (\<lambda> IT. Y \<noteq> {}) otherwise (\<lambda>IT. IT = {})" .
 
text_raw {*\DefineSnippet{expandable_modes}{*}
abbreviation funct_2_mode_1   ("Function-of _, _" [90,90] 190)
where "Function-of X,Y \<equiv> (X,Y: quasi-total) \<bar> (PartFunc-of X,Y)"
text_raw {*}%EndSnippet*}

     
mtheorem funct_2_th_2:
  "f be Function-of dom f, rng f"
proof-
  have "dom f c= dom f" "rng f c= rng f" using tarski_def_3 by mauto
  hence A1[ty]: "f be Relation-of dom f,rng f" using relset_1_th_4 by ty_simp
  show "f be Function-of dom f, rng f"
  proof (cases "rng f={}")
     assume "rng f \<noteq>{}"
     thus "f be Function-of dom f, rng f" using A1 funct_2_def_1(1) by ty_simp
   next
     assume A2: "rng f = {}"
      hence "f={}" using relat_1_th_41[of f] by ty_simp
     hence "f be (dom f), (rng f):quasi-total" using A1 A2 funct_2_def_1I by mauto
     thus "f be Function-of dom f, rng f" by mauto
  qed
qed

mtheorem funct_2_th_3:
  "rng f \<subseteq> Y implies f be Function-of dom f, Y"
proof
  assume A0: "rng f \<subseteq> Y" 
  hence "dom f c= dom f" "rng f c= Y" using tarski_def_3 by mauto
  hence A1[ty]: "f be Relation-of dom f,Y" using relset_1_th_4 by ty_simp
  show "f be Function-of dom f, Y"
  proof (cases "rng f={}")
    assume "rng f \<noteq>{}"
     hence "Y \<noteq> {}" using xboole_1_empty[OF _ _ A0] by mauto
     thus "f be Function-of dom f, Y" using A1 funct_2_def_1I[of "dom f" Y f] by ty_simp
   next
     assume A2: "rng f = {}"
      hence "f={}" using relat_1_th_41[of f] by ty_simp
     hence "f be (dom f), Y:quasi-total" using A1 A2 funct_2_def_1I by mauto
     thus "f be Function-of dom f, Y" by ty_simp
  qed
qed  

  
  
  
text_raw {*\DefineSnippet{funct_2_th_2}{*}
theorem "\<forall>x : object. \<not> x is Function-of dom x, rng x \<longrightarrow> \<not> x is Function"
  using funct_2_th_2 by mauto
text_raw {*}%EndSnippet*}


text_raw {*\DefineSnippet{funct_2_cl_ex}{*}
mtheorem
  mlet "X be set", "Y be set"
  "cluster X,Y: quasi-total for  PartFunc-of X,Y"
text_raw {*}%EndSnippet*}
proof(standard)
  show "inhabited (Function-of X,Y)"
  proof(cases "Y={}")
    case T: True
      have "{} c= [:X,Y:]" using xb1 by (intro tarski_def_3I) mauto
      hence A: "{} be PartFunc-of X,Y" using Subset_of_rule T by mauto
      have "dom {}={}" by (intro empty1) mauto
      then have "{} be Function-of X,Y" using A funct_2_def_1I[of X Y "{}"] T by mauto
      thus ?thesis using bexI inhabited_def by auto
   next
    case K: False
      then obtain y where
         "y be object" and A1: "y in Y" using xboole_0_def_1 empty1[of Y] by mauto
      have "ex f be Function st dom f = X \<and> rng f c= {y}" using funct_1_th_5[of y X] by mauto
      then obtain f where
        [ty]: "f be Function" and A3:"dom f = X \<and> rng f c= {y}" by auto
      have "rng f c= Y" using A1 tarski_def_3 A3 tarski_def_1
        by (intro tarski_def_3I) mauto
      hence "f be PartFunc-of X,Y" using relset_1_th_4 xboole_0_def_10 A3 by inst_pass_auto
      hence "f be Function-of X,Y" using funct_2_def_1 A3 K by mauto
      thus ?thesis using bexI inhabited_def by auto
    qed
qed

theorem funct_2_sch_1:
  assumes [ty]: "X be set" "Y be set" and
         P1:"for x being object st x in X holds (ex y being object st y in Y & P(x,y))" and
         P2:"for x,y1,y2 being object st x in X &  P(x,y1) & P(x,y2) holds y1 = y2"
  shows "ex f being Function-of X, Y st 
        (for x being object st x in X holds P(x,f. x)) "     
proof-
   let ?Z = "\<lambda>x y. x in X & P(x,y)"
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
     show "ex f being Function-of X, Y st
        (for x being object st x in X holds P(x,f. x))"
       proof (intro bexI[of _ Q] conjI)
         have D: "dom Q = X"
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
            hence "ex y being object st y in Y & P(x,y)" using P1 by auto   
            then obtain y where
              "y be object" and B1:"y in Y & P(x,y)" by auto
            hence "[x,y] in Q" using B A2 by auto            
            thus "x in dom Q" using xtuple_0_def_12 by mauto
          qed mauto
        qed mauto
        have R:"rng Q c= Y" 
        proof(standard,auto)
           fix y
           assume B: "y in rng Q"
           then obtain x where
             "x be object" and B1: "x in dom Q & y= Q. x" using funct_1_def_3 by ty_auto
           hence "[x,y] in Q" using funct_1_def_2 by ty_auto
           thus "y in Y" using A2 by auto
          qed mauto
        thus "Q be Function-of X,Y" using  D funct_2_th_3 T2 P by ty_auto  
        show "for x st x in X holds P(x,Q. x)"
         proof (intro ballI impI)
            fix x
            assume B: "x in X"
            hence "[x,Q. x] in Q" using D funct_1_def_2 by ty_auto  
            thus "P(x,Q. x)" using A2 by auto
         qed simp_all
    qed mauto
qed  
  
  
mtheorem funct_2_th_4:
  "for f being (Function-of X,Y) st (Y \<noteq> {} \<and> x in X) holds f . x in rng f"
proof (intro ballI, rule impI )
  show "inhabited(Function-of X,Y)" by auto
  fix f
  assume T[ty]:"f be (Function-of X,Y)"
  assume A1: "Y \<noteq> {} \<and> x in X"
  have "dom f = X" using funct_2_def_1E[of X Y f] A1 by ty_auto
  thus "f . x in rng f" using funct_1_def_3 A1 by mauto
qed

mtheorem funct_2_th_5:
  "for f being Function-of X,Y st Y \<noteq> {} \<and> x in X holds f . x in Y"
proof (intro ballI, rule impI)
 show I: "inhabited(Function-of X,Y)" by auto
  fix f
  assume [ty]:"f be (Function-of X,Y)"
  assume "Y \<noteq> {} \<and> x in X"
  hence T4: "f . x in rng f" using funct_2_th_4[of x Y X] I by ty_auto
  have "rng f c= Y" using relat_1_def_19[of Y f] by mauto
  thus "f . x in Y" using T4 tarski_def_3 by infer_auto
qed

mdef funct_2_def_3 ("_ -onto" [95] 100)where
mlet "Y be set"  
"attr Y -onto for Y-valued\<bar>Function means (\<lambda>IT. rng IT = Y)".

mdef funct_2_def_4 ("_ -bijective" [95] 100)where
  mlet "Y be set" 
  "attr Y -bijective for Y-valued\<bar>Function means (\<lambda>IT. IT is Y-onto \<bar> one-to-one)".

text_raw {*\DefineSnippet{funct_2_cl_11}{*}
mtheorem 
 mlet "Y be set"
 "cluster Y -bijective \<rightarrow> Y -onto \<bar> one-to-one for Y-valued \<bar> Function"
  text_raw {*}%EndSnippet*}
proof  (standard,intro ballI impI) 
  fix F assume [ty]:" F be Y-valued \<bar> Function" " F be Y -bijective"
  show "F is Y -onto \<bar> one-to-one"
    using funct_2_def_4E by mauto
qed mauto

text_raw {*\DefineSnippet{funct_2_cl_12}{*}
mtheorem 
  mlet "Y be set" 
 "cluster  Y -onto \<bar> one-to-one \<rightarrow> Y -bijective for Y-valued \<bar> Function"
  text_raw {*}%EndSnippet*}
proof  (standard,intro ballI impI) 
  fix F assume [ty]:" F be Y-valued \<bar> Function" " F be Y -onto \<bar> one-to-one"
  show "F is Y -bijective"
    using funct_2_def_4I by mauto
qed mauto

text_raw {*\DefineSnippet{funct_2_def_5}{*}
mtheorem funct_2_def_5:
  mlet "C be non empty\<bar>set","D be set",
       "f be (Function-of C,D)"," c be Element-of C"
   "redefine func f . c \<rightarrow> Element-of D"
text_raw {*}%EndSnippet*}
proof(standard)
  show "(f . c)  be (Element-of D)"
  proof ( cases "D is empty")
    assume A1: "D is empty"
    hence "D={}" using empty1 by auto
    hence "f = {}" using funct_2_def_1E[of C D f] by mauto
    hence "dom f={}" using empty1[of "proj1 {}"] by mauto
    hence "f . c = {}" using funct_1_def_2[of f] xb by mauto
    thus "(f . c) be (Element-of D)" using A1 subset_1_def_1 by mauto
  next
    assume "not D is empty"
    hence A2:"D \<noteq> {}" by mauto
    have "c in C" using subset_1_def_1[of C c] by mauto
    hence "(f . c) in D" using A2 funct_2_th_5[of c D C] by mauto
    thus "(f . c) be Element-of D" using Element(6) by mauto
  qed
qed

text_raw {*\DefineSnippet{funct_2_def_7}{*}
mtheorem funct_2_def_7:
  mlet "A be set"," B be set",
      "f1 be Function-of A,B", "f2 be Function-of A,B"
  " redefine pred f1 = f2 means
      for a be Element-of A holds f1 . a = f2 . a"
text_raw {*}%EndSnippet*}
proof
  show " f1 = f2 \<longleftrightarrow> (for a be Element-of A holds f1 . a = f2 . a)"
  proof(rule iffI3)
    show " f1 = f2 \<longrightarrow> (for a be Element-of A holds f1 . a = f2 . a)" by auto
    assume A: "for a be Element-of A holds f1 . a = f2 . a"
    show "f1=f2"
    proof(intro tarski_th_2 iffI3)
      fix a
      show "a in f1 \<longrightarrow> a in f2"
      proof
        assume A2: "a in f1"
        then obtain x y where
           A3: "x be object" "y be object" "a=[x,y]" using relat_1_def_1[of f1] by mauto
        hence A4:"x in dom f1 \<and> y = f1 .x" using funct_1_th_1[of f1 y x] A2 by mauto
        have "y in proj2 f1" using xtuple_0_def_13 A2 A3 by mauto
        hence "y in B" using relat_1_def_19 [of B f1] tarski_def_3E[of "proj2 f1" B] by mauto
        hence A5: "dom f1 = A" "dom f2 = A" using funct_2_def_1E xb[of y] by mauto
        hence "f1 . x = f2 . x" using A A4 Element(6) by mauto
        hence "[x,y] in f2" using funct_1_th_1[of f2 y x] A3 A4 A5 by mauto
        thus "a in f2" using A3 by simp
      qed
     assume A2: "a in f2"
        then obtain x y where
           A3: "x be object" "y be object" "a=[x,y]" using relat_1_def_1[of f2] by mauto
        hence A4:"x in dom f2 \<and> y = f2 .x" using funct_1_th_1[of f2 y x] A2 by mauto
        have "y in proj2 f2" using xtuple_0_def_13 A2 A3 by mauto
        hence "y in B" using relat_1_def_19[of B f2] tarski_def_3E[of _ B] by mauto
        hence A5: "dom f1 = A" "dom f2 = A" using funct_2_def_1E xb[of y] by mauto
        hence "f1 . x = f2 . x" using A A4 Element(6) by mauto
        hence "[x,y] in f1" using funct_1_th_1[of f1 y x] A3 A4 A5 by mauto
        thus "a in f1" using A3 by simp
      qed mauto
  qed
qed

text_raw {*\DefineSnippet{funct_2_th_50}{*}
mtheorem funct_2_th_50:
  "for y be object, X be non empty\<bar>set holds
     for f1,f2 be Function-of X,{y} holds f1=f2"
proof(intro ballI)
  fix y X
  assume T0[ty]: "y be object" "X be non empty\<bar>set"
  show "inhabited(Function-of X,{y})" "inhabited(Function-of X,{y})" by mauto
  fix f1
  assume [ty]:"f1 be Function-of X,{y}"
  fix f2 assume[ty]: "f2 be Function-of X,{y}"
  show "f1 = f2"
  proof (rule funct_2_def_7I[of X "{y}" f1 f2],ty_simp)
text_raw {*}%EndSnippet*}
   show "for a be Element-of X holds f1 . a = f2 . a"
       proof
         fix a assume A1[ty]: "a be Element-of X"
         have A2: "a in X" using Element(1)[of X a]  ty by auto
         have "{y}\<noteq>{}" using xb tarski_def_1[of y y] by auto
         hence "f1 .a in {y}" "f2 .a in {y}"
           using funct_2_th_5[of a "{y}" X] A2 by mauto
           thus "f1 .a = f2 .a" using tarski_def_1 by auto
        qed simp
      qed mauto
qed simp_all

mtheorem funct_2_lm_1:
  mlet "f be Function "," g be Function"
  "rng f c= dom g implies dom f = dom (g*`f)"
proof (intro impI xboole_0_def_10I conjI)
  assume A0:"rng f c= dom g"
       show "dom f \<subseteq> dom (g*`f)"
          proof (standard,auto)
            fix x
            assume K: "x in dom f"
            hence "f. x in dom g" using funct_1_def_3[of f] tarski_def_3E[OF _ _ A0] by mauto
            thus "x in dom (g*`f)" using funct_1_th_11[of g f x] K by mauto
          qed mauto
          show "dom (g*`f) \<subseteq> dom f"
           proof (standard,auto)
            fix x
            assume "x in dom (g*`f)"
            thus "x in dom f" using funct_1_th_11[of g f x] by mauto
          qed mauto
        qed mauto

 mtheorem funct_2_lm_2:
  mlet "f be Function","g be Function"
  "rng f c= dom g implies rng (g*`f) c= rng g"
 proof(standard,standard,auto)
   assume  A1: "rng f c= dom g"
   fix y
    assume "y in rng (g*`f)"
    then obtain x where
      C1: "x be object" "x in dom (g*`f)" "(g*`f). x = y" using funct_1_def_3 by mauto
    have "x in dom f \<and> f. x in dom g" using funct_1_th_11[of g f x] C1 by mauto
    hence "g.(f. x) = (g*`f). x" "g.(f. x) in rng g" using funct_1_th_12[of g f x]
      funct_1_def_3[of g] C1 by mauto
    thus "y in rng g" using C1 by simp
qed mauto

text_raw {*\DefineSnippet{funct_2_def_11}{*}
mdef funct_2_def_11 ("_ '/*`[_, _] _" [10,0,0,10] 90) where
   mlet "X be set", "Z be set", "Y be (non empty)\<bar>set",
      "f be Function-of X,Y","p be (Z-valued) \<bar>Function"
   "assume rng f c= dom p func p /*`[X, Z] f \<rightarrow>
             Function-of X,Z equals p*`f"
text_raw {*}%EndSnippet*}
proof -
   assume A1: "rng f c= dom p"
    have A22: "rng p c= Z" using relat_1_def_19[THEN iffD1] by mauto
    let ?y = "the (Element-of Y)"
    have "Y \<noteq> {}" using xb1 ty xboole_0_def_1 empty2 by auto
    hence B3: "dom f = X" using funct_2_def_1E by mauto
    have A2: "dom f = dom (p*`f)" using funct_2_lm_1[of f p] A1 by mauto
        have A3: "rng (p*`f) c= Z"
        proof(standard,auto)
             fix y
             assume "y in rng (p*`f)"
             then obtain x where
               C1: "x be object" "x in dom (p*`f)" "(p*`f). x = y" using funct_1_def_3 by ty_auto
             have "x in dom f \<and> f. x in dom p" using funct_1_th_11[of p f x] C1 B3 by ty_auto
             hence "p.(f. x) = (p*`f). x" "p.(f. x) in rng p" using funct_1_th_12[of p f x] C1
               funct_1_def_3 by mauto
             thus "y in Z" using tarski_def_3E[OF _ _ A22] C1 by mauto
          qed mauto
       hence T3: "p*`f be Relation-of X,Z" using A2 B3 relset_1_th_4[of Z X] xboole_0_def_10 by infer_auto
  show "p*`f be (Function-of X,Z)"
  proof(cases "Z={}")
    case T: True
      have "{} c= [:X,Z:]" using xb1 by (intro tarski_def_3I) mauto
      hence A: "{} be PartFunc-of X,Z" using Subset_of_rule[of "{}" "[:X,Z:]"] T by mauto
      have "dom {}={}" using empty1[of "dom {}"] by infer_auto
      hence A: "{} be Function-of X,Z" using A funct_2_def_1I[of X "{}" "{}"] T by mauto
      have "rng (p*`f) ={}" using A3 T xboole_0_def_10[of "rng (p*`f)" "{}"] xb[simplified] tarski_def_3I[of "{}"] by mauto
      hence "(p*`f) ={}" using relat_1_th_41[of "p*`f"]  by mauto
      thus "p*`f be (X,Z: quasi-total)\<bar> (PartFunc-of X,Z)" using A funct_2_def_1E[of "p*`f" X Z] T3 T by auto
  next
     case K: False
    hence A4: "p*`f be Function_like \<bar> (Relation-of X,Z)" using T3 by mauto
    hence "p*`f is (X,Z: quasi-total) \<or> (p*`f = {} \<and> Z={})" using funct_2_def_1I[of X Z "p*`f"] A2 A3 K B3 by mauto
    thus "p*`f be (X,Z: quasi-total) \<bar> (PartFunc-of X,Z)" using A4 K by auto
   qed
qed mauto

mtheorem funct_2_def_10:
  mlet "X be set"
  "redefine func id X \<rightarrow> Function-of X,X"
proof
  have A1:"dom (id X) = X" "rng (id X) = X" using relat_1_id_dom relat_1_id_rng by mauto
  hence T1[ty]:"id X be Relation-of X,X" using relset_1_th_4[of X X] xboole_0_def_10 by mauto
  show "id X be Function-of X,X"
  proof (cases "X={}")
    case I:True
      hence "id X={}" using A1 relat_1_th_41[of "id X",rule_format] by mauto
      hence "id X is X , X : quasi-total" using T1 funct_2_def_1I[of X X "id X"] I by mauto
      thus ?thesis using T1 by mauto
  next
    case False
       thus ?thesis using A1 funct_2_def_1I[of X X "id X"] T1 by mauto
  qed
qed


mdef funct_2_def_2 ("Funcs'( _ , _ ')") where
  mlet "X be set", "Y be set"
  "func Funcs(X,Y) \<rightarrow> set means
     \<lambda>it. \<forall>x : object. 
         x in it \<longleftrightarrow> (ex f being Function st x = f \<and> dom f = X \<and> rng f c= Y)"
proof-
   let ?P = "\<lambda>x. ex f being Function st x = f \<and> dom f = X \<and> rng f c= Y"
    have A0:"bool [:X,Y:] be set" by infer_auto
     obtain IT where
   [ty]:"IT be set" and A1: "for x being object holds x in IT \<longleftrightarrow> x in bool [:X,Y:] \<and> ?P(x)" using xboole_0_sch_1[OF A0, of ?P] by auto
     show "ex IT be set st \<forall>x : object.  x in IT \<longleftrightarrow> (ex f being Function st x = f \<and> dom f = X \<and> rng f c= Y)"
     proof(rule bexI[of _ IT],rule ballI,rule iffI3)
       fix x assume [ty]:"x be object"
       show "x in IT \<longrightarrow> (ex f being Function st x = f \<and> dom f = X \<and> rng f c= Y)" using A1 by auto
       assume A2: "ex f being Function st x = f \<and> dom f = X \<and> rng f c= Y"
       then obtain f where
         [ty]:"f be Function" and A3: "x=f \<and> dom f = X \<and> rng f c= Y" by auto
       have A4: "rng f c= Y" using A2 A3 by auto
       have "dom f c= X" using A3 xboole_0_def_10 by infer_auto
       hence A5: "[:dom f,rng f:] c= [:X,Y:]" using A4 A3(1) zfmisc_1_th_96[of Y "rng f" X "dom f"] by infer_auto
       have "f c= [:dom f,rng f:]" using relat_1_th_7[of f] A2 by ty_auto
       hence "f c= [:X,Y:]" using A5 tarski_def_3 tarski_0_1 by auto
       hence "f in bool [:X,Y:]" using zfmisc_1_def_1 by infer_auto
       thus "x in IT" using A1 A2 A3 by auto
     qed ty_auto
next
  fix A1 A2
  assume [ty]:"A1 be set" and A1: "(\<forall>x : object. 
         x in A1 \<longleftrightarrow> (ex f being Function st x = f \<and> dom f = X \<and> rng f c= Y))" and
        [ty]: "A2 be set" and A2:"\<forall>x : object. 
         x in A2 \<longleftrightarrow> (ex f being Function st x = f \<and> dom f = X \<and> rng f c= Y)"
    {
      fix x
      assume Z1: "x be object"
      have "x in A1 \<longleftrightarrow> (ex f being Function st x = f \<and> dom f = X \<and> rng f c= Y)" using Z1 A1 by auto
      then have "x in A1 \<longleftrightarrow> x in A2" using Z1 A2 by auto
    }
  thus "A1 = A2" by (intro tarski_th_2) ty_auto
qed simp_all
  
text_raw {*\DefineSnippet{funct_2_sch_4}{*}  
theorem funct_2_sch_4:
  assumes [ty]: "C be non empty\<bar>set"   "D be non empty\<bar>set"
    and T0: "\<forall>x:Element-of C. F(x) be Element-of D"
  shows "\<exists>f:Function-of C,D. \<forall>x:Element-of C. (f . x) = F(x)"
text_raw {*}%EndSnippet*}
proof-
  obtain f where
    [ty]:"f be  Function" and A1:"dom f = C \<and> (for x st x in C holds f .x = F(x))" 
    using funct_1_sch_Lambda[of C F] by ty_auto
  have "rng f \<subseteq> D"
  proof(standard,auto)
    fix y assume "y in rng f"
    then obtain x where
      A2: "x in dom f \<and>y=f . x" using funct_1_def_3 by ty_auto
    hence "x is Element-of C" using Element_of A1 by ty_auto
    hence  "f .x = F(x)" "F(x) is Element-of D" using A1  Element_of1 T0 by ty_auto
    thus "y in D" using Element_of1 A2 by ty_auto
  qed mauto
  hence [ty]:"f be Function-of C,D" using A1 funct_2_th_3 by ty_auto
  show "\<exists>f:Function-of C,D. \<forall>x:Element-of C. (f .x) = F(x)"
  proof(rule bexI[of _ f],auto)
    fix x assume "x is Element-of C"
    hence "x in C" using Element_of1[of C x] by ty_auto
    thus "f .x = F(x)" using A1  Element_of1 by auto  
  qed ty_auto
qed  

mtheorem funct_2_cl_Funcs1:
  mlet "A be set", "B be non empty\<bar>set"
 "cluster Funcs(A,B) \<rightarrow> non empty"
proof
  obtain b where
    A1:  "b in B" using xboole_0_def_1[of B] by ty_auto
  let ?F ="A \<midarrow>> b"
  have A: "dom ?F = A" "rng ?F c= {b}" using funcop_1_th_13 by ty_auto

  have "rng ?F c= B"
  proof(standard,auto)
    fix x assume "x in rng ?F"
    then show "x in B " using A A1 tarski_def_3 tarski_def_1 by inst_pass_auto
  qed mauto
  hence "?F in  Funcs(A,B)" using A funct_2_def_2 by inst_pass_auto
  then show "Funcs(A,B) is non empty" using xboole_0_def_1 by ty_auto
qed

mtheorem funct_2_cl_Funcs:
  mlet "X be set"
  "cluster Funcs(X,X) \<rightarrow> non empty"
proof
  have "dom id X=X" "rng id X=X"
    using relat_1_id_dom relat_1_id_rng by mauto
  hence "id X in Funcs(X,X)" using funct_2_def_2 xboole_0_def_10 by mauto
  thus "Funcs(X,X) is non empty" using xboole_0_def_1 bexI by ty_auto
qed

text_raw {*\DefineSnippet{Action}{*}
abbreviation funct_2_action ("Action-of _ , _") where
  "Action-of O, E \<equiv> Function-of O,Funcs(E,E)"
text_raw {*}%EndSnippet*}

theorem funct_2_cl_action[ex]:
  assumes [ty]: "O be set" "E be set"
  shows "inhabited(Action-of O,E)"
  by mauto

abbreviation pboole_def_1 ("ManySortedSet-of _" 190) where
  "ManySortedSet-of I \<equiv> I:total \<bar> I-defined \<bar> Function"

mtheorem pboole_def_1_th_1:
  "for F be Function st dom F=X holds F be ManySortedSet-of X"
proof(intro ballI impI)
  obtain A where "A=X" by auto
  fix F
  assume [ty]:"F be Function"
  assume A: "dom F=X"
  hence [ty]:"F be X-defined" using xboole_0_def_10 relat_1_def_18I by mauto
  hence" F be X:total" using A partfun_1_def_2I by ty_auto
  thus "F be ManySortedSet-of X" by ty_auto
qed simp_all

mtheorem pboole_cl_ex:
  mlet "I be set"
  "cluster I:total \<bar> I-defined for Function"
proof(standard)
  have "inhabited (Function-of I,{I})" by mauto
  then obtain F where
    A1[ty]: "F be Function-of I,{I}" using inhabited_def by auto  
  have [ty]:"F is Function" by ty_auto
  have "{I} be set" by mauto
  hence "bool [:I,{I}:] be set" by mauto
  hence "F be set" using A1 subset_1_def_1(1) by mauto
  have "I in {I}" using tarski_def_1 by simp
  hence "{I} \<noteq>{}" using xb by auto
  hence "dom F = I" using funct_2_def_1E by mauto
  hence "F is I : total \<bar> I -defined \<bar> Function" using pboole_def_1_th_1[of I F] by mauto
  thus "inhabited(ManySortedSet-of I)" ..
qed

mtheorem funct_2_cl_comp:
  mlet "I be set","f be non-empty\<bar>I:total \<bar>I-defined\<bar>Function"
  "cluster I:total \<bar>I-defined\<bar> f-compatible for Function"
proof
  let ?P = "\<lambda>x. the Element-of f .x"
  obtain F where
    [ty]: "F be Function" and A2: "dom F=I" 
    "for x be object st x in I holds F .x = ?P(x)" 
    using funct_1_sch_Lambda[of I ?P] by ty_auto
  have A[ty]:"F is I-defined\<bar>I:total" using pboole_def_1_th_1 A2 by ty_auto
  have A3: "dom f=I" using partfun_1_def_2E by mauto
  have "F is f-compatible"
  proof(intro funct_1_def_14I,auto)
      fix x assume A4: "x in dom F"
      hence "f. x in rng f" using A3 A2 funct_1_def_3 by mauto
      hence A5: "f. x \<noteq> {}" using funct_1_def_9 by mauto
      have "F .x = the Element-of f .x" using A2 A4 by auto
      hence "(F. x) be (Element-of f .x)" by mauto
      thus "F .x in f .x" using Element(4) A5 by mauto
  qed ty_auto
  hence "F be I:total \<bar> I-defined\<bar> f-compatible \<bar>Function" by ty_auto
  thus "inhabited(I:total \<bar> I-defined\<bar>f-compatible \<bar> Function)" unfolding inhabited_def ..
qed

reserve A,B for set

mtheorem funcop_cl[rule_format]:
  "y in B implies (A \<midarrow>> y) is (Function-of A,B)"
proof
  assume A0: "y in B"
  hence "{y} c= B" using tarski_def_1 tarski_def_3 by mauto
  hence "[:A, {y}:] c= [:A,B:]" using zfmisc_1_th_96[of B "{y}"] xboole_0_def_10[of A A] by mauto
  hence W0:"[:A,{y}:] be Subset-of [:A,B:]" using Subset_of_rule by auto
  hence W1: "[:A,{y}:] be Relation-of A,B" by mauto
  hence [ty]:"(A \<midarrow>> y) be Relation-of A,B" using funcop_1_def_2 by ty_auto
  hence W2: "(A \<midarrow>> y) be PartFunc-of A,B" by ty_auto
  have "dom (A\<midarrow>> y) = A" "B\<noteq>{}" using funcop_1_th_13 A0 xb by ty_auto
  hence "(A\<midarrow>> y) is (A,B: quasi-total)" using funct_2_def_1I W2 by mauto
  thus "(A \<midarrow>> y) be (Function-of A,B)" using W2 by mauto
qed



mdef card_3_def_5 ("product _" [105] 105) where
  mlet "f be Function"
  "func product f \<rightarrow> set means
     \<lambda>it. \<forall>x : object. 
         x in it \<longleftrightarrow> (ex g st x = g \<and> dom g = dom f \<and>
       (for y being object st y in dom f holds g. y in f. y))"
proof-
  let ?P = "\<lambda>x.  ex g be Function st x = g \<and> dom g = dom f \<and>
      (for x being object st x in dom f holds g. x in f. x)"
    have A0: "Funcs(dom f, union rng f) be set" by mauto
     obtain IT where
   A1:"IT be set"  "for x being object holds x in IT \<longleftrightarrow> x in Funcs(dom f, union rng f) \<and> ?P(x)" using xboole_0_sch_1[OF A0, of ?P]
       by auto
     show "ex IT be set st \<forall>x : object.  x in IT \<longleftrightarrow> ?P(x)"
     proof(intro bexI[of _ IT] ballI iffI3)
       show "IT be set" using A1(1) by simp
       fix x assume "x be object"
       show "x in IT \<longrightarrow> ?P(x)" using A1 by auto
       assume A2: "?P(x)"
       then obtain g where
         [ty]:"g be Function" and A3: "x=g" "dom g = dom f" "for x being object st x in dom f holds g. x in f. x"
         by auto
       have "rng g c= union rng f"
       proof(standard,auto)
         fix y assume "y in rng g"
         then obtain x where
           A4: "x be object" "x in dom g \<and> g .x =y" using funct_1_def_3 A3(1) by mauto
         have "y in f. x" "f. x in rng f" "f. x be set" using A3 A4 funct_1_def_3 by mauto
         thus "y in union rng f" using tarski_def_4[of "proj2 f"] bexI by mauto
         qed mauto
       thus "x in IT" using A1(2) A2 funct_2_def_2 A3 by mauto
     qed simp_all
next
  fix A1 A2
  assume [ty]: "A1 be set"  "A2 be set" and A1: "(\<forall>x : object. 
         x in A1 \<longleftrightarrow> (ex g be Function st x = g \<and> dom g = dom f \<and>
      (for x being object st x in dom f holds g. x in f. x)))" and
        A2: "\<forall>x : object. 
         x in A2 \<longleftrightarrow> (ex g be Function st x = g \<and> dom g = dom f \<and>
      (for x being object st x in dom f holds g. x in f. x))"
    {
      fix x
      assume Z1: "x be object"
      have "x in A1 \<longleftrightarrow> (ex g be Function st x = g \<and> dom g = dom f \<and>
      (for x being object st x in dom f holds g. x in f. x))" using Z1 A1 by auto
      then have "x in A1 \<longleftrightarrow> x in A2" using Z1 A2 by auto
    }
  thus "A1 = A2" by (intro tarski_th_2) ty_auto
qed simp_all

mtheorem card_3_cl:
  mlet "f be non-empty\<bar>Function"
  "cluster product f \<rightarrow> non empty"
proof
  have A2: "(dom f) be set \<and> f be non-empty \<bar>   (dom f) : total \<bar>  (dom f) -defined \<bar> Function" using pboole_def_1_th_1 by mauto
  hence "inhabited((dom f):total \<bar>(dom f)-defined \<bar> f-compatible \<bar> Function)" using ex by simp
  then obtain g where
     A3[ty]: "g be (dom f):total \<bar>(dom f)-defined \<bar> f-compatible\<bar>Function" using inhabited_def by blast
  have "dom g=dom f" using partfun_1_def_2E by ty_auto
  hence "for y being object st y in dom f holds g. y in f. y" using funct_1_def_14[of f g,THEN iffD1,simplified] by ty_auto
  hence "g in product f" using partfun_1_def_2E[of "proj1 f" g] card_3_def_5 by mauto
  thus "product f is non empty" using xboole_0_def_1 by mauto
qed
end
