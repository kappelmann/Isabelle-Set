theory zfmisc_1
imports xboole_0 xfamily xtuple_0
begin

reserve x,y,z,x1,x2,y1,y2 for object
reserve X,Y,Z for set

section "ZFMISC1"
reserve X,Y,N,M for set

text_raw {*\DefineSnippet{zfmisc_1_def_1}{*}

mdef zfmisc_1_def_1   ("bool _" [110] 110) where
   mlet "X be set"
   "func (bool X) \<rightarrow> set means
     \<lambda>it. (\<forall>Y. Y in it \<longleftrightarrow> Y \<subseteq> X)"
text_raw {*}%EndSnippet*}
proof-
       let ?IT="\<lambda>x. x c= X"
       obtain M where
          [ty]: "M be set" and A1: "X in M" "(for X,Y holds X in M \<and> Y c= X \<longrightarrow> Y in M) \<and>
            (for X st X in M ex Z st Z in M \<and> (for Y st Y c= X holds Y in Z)) \<and>
            (\<forall>X.  X c= M \<longrightarrow> (X, M areequipotent \<or> X in M))"
         using tarski_a_th_1[THEN bspec, of X] ex ty by blast
     obtain IT where
          [ty]:"IT be set" and A2: "for Y being object holds (Y in IT \<longleftrightarrow> Y in M \<and> Y c= X)"
          using xboole_0_sch_1[of M ?IT] by infer_auto
       (* Mizar's "take IT" abbreviates the whole show with a proof block by existential introduction *)
       show "ex IT being set st (for Y being set holds (Y in IT \<longleftrightarrow> Y c= X))"
          proof (rule bexI[of _ IT])
            show "IT be set" using A2 by infer_auto
            show "for Y being set holds (Y in IT \<longleftrightarrow> Y c= X)"
            proof(rule ballI,rule iffI2)
              fix Y assume [ty]:"Y be set"
              show "Y in IT \<longrightarrow> Y c= X" using A1 A2 by auto
              show "Y c= X \<longrightarrow> Y in IT"
              proof
                assume A: "Y c= X"
                hence "Y in M" using A1(2)[THEN conjunct1,THEN bspec,of X] A1(1) by infer_auto
                thus "Y in IT" using A2 A by auto
              qed
            qed simp_all
          qed simp_all
  next
     fix x y
       assume [ty]: "x be set" and [ty]: "y be set" and A3: "(for Z being set holds (Z in x \<longleftrightarrow> Z c= X))"
          and A4: "(for Z being set holds (Z in y \<longleftrightarrow> Z c= X))"
       thus "x = y" using xfamily_sch_3[OF _ _  A3 A4] by auto
qed simp_all

text_raw {*\DefineSnippet{zfmisc_1_def_2}{*}

mdef zfmisc_1_def_2 ("[:_ ,_:]") where
  mlet "X1 be set", "X2 be set"
  "func [: X1, X2 :] \<rightarrow> set means \<lambda>it. (\<forall>z.  z in it \<longleftrightarrow> (ex x, y st x in X1 \<and> y in X2 \<and> z = [x, y]))"
text_raw {*}%EndSnippet*}
proof-
      let ?X1="\<lambda>it1. ex x,y st x in X1 \<and> y in X2 \<and> it1 = [x,y]"
     have AA: "(bool(bool(X1 \<union> X2))) be set" using zfmisc_1_def_1 by infer_auto
    obtain X where
    [ty]: "X be set " and A2: "for z being object holds z in X \<longleftrightarrow> (z in (bool(bool(X1 \<union> X2))) \<and> ?X1(z))" using
                     xboole_0_sch_1[OF AA, of ?X1] by auto
       show "ex X being set st (\<forall>z.  z in X \<longleftrightarrow> (ex x, y st x in X1 \<and> y in X2 \<and> z = [x, y]))"
          proof (rule bexI[of _  X])
             show "\<forall>z.  z in X \<longleftrightarrow> (ex x, y st x in X1 \<and> y in X2 \<and> z = [x, y])"
                proof (intro ballI, rule iffI2)
                  fix z
                  assume [ty]: "z be object"
                  show "z in X \<longrightarrow> (ex x, y st x in X1 \<and> y in X2 \<and> z = [x, y])" using A2 by simp
                  show "(ex x, y st x in X1 \<and> y in X2 \<and> z = [x, y]) \<longrightarrow> z in X"
                     proof
                       assume "ex x, y st x in X1 \<and> y in X2 \<and> z = [x, y]"
                       then obtain x y where
                          "x be object \<and> y be object" and A3: "x in X1" and A4:"y in X2" and A5:  "z = [x, y]" by auto
                       have A5': "z = {{x,y},{x}}" using A5 tarski_def_5 by simp
                       have "{x,y} c= X1 \<union> X2"
                         proof(standard,auto)
                           fix z
                           assume "z in {x,y}"
                           thus "z in X1 \<union> X2" using A3 A4 xboole_0_def_3 tarski_def_2 by infer_auto
                         qed infer_auto
                       hence A6: "{x,y} in bool(X1 \<union> X2)" using zfmisc_1_def_1 by infer_auto
                       have "{x} c= X1 \<union> X2"
                         proof(standard,auto)
                           fix z
                           assume "z in {x}"
                           thus "z in X1 \<union> X2" using A3 A4 xboole_0_def_3 tarski_def_1 by infer_auto
                         qed infer_auto
                       hence A7: "{x} in bool(X1 \<union> X2)" using zfmisc_1_def_1 by infer_auto
                       hence "{{x,y},{x}} c= bool(X1 \<union> X2)" using A6 tarski_def_2 tarski_def_3 by infer_auto
                       hence "{{x,y},{x}} in bool(bool(X1 \<union> X2))" using zfmisc_1_def_1 by infer_auto
                       thus "z in X" using A2 A3 A4 A5 A5' by auto
                     qed
                qed simp_all
              qed infer_auto
    next
      fix IT1 IT2 assume [ty]: "IT1 be set" "IT2 be set" and
       A1:"\<forall>z.  z in IT1 \<longleftrightarrow> (ex x, y st x in X1 \<and> y in X2 \<and> z = [x, y])"
       and A2:"\<forall>z.  z in IT2 \<longleftrightarrow> (ex x, y st x in X1 \<and> y in X2 \<and> z = [x, y])"
       show "IT1 = IT2" using xboole_0_sch_3[of IT1 IT2 "\<lambda>z . (ex x, y st x in X1 \<and> y in X2 \<and> z = [x, y])"] A1 A2 by infer_auto
    qed simp_all


mdef zfmisc_1_def_3 ("[:_, _, _:]") where
  mlet "X1 be set", "X2 be set", "X3 be set"
  "func [: X1,X2,X3 :] \<rightarrow> set equals [:[:X1,X2:],X3:]"
proof-
  show "[:[:X1,X2:],X3:] be set" by infer_simp
qed


abbreviation triple ("[ _ , _ , _]") where
  "[x,y,z] \<equiv> [[x,y],z]"

reserve X1,X2,X3,X4 for set
mtheorem zfmisc_3:
  "x in [: X1,X2,X3 :] \<Longrightarrow> ex x1,x2,x3 be object st x = [x1,x2,x3] \<and> x1 in X1 \<and> x2 in X2 \<and> x3 in X3"
proof-
  assume "x in [: X1,X2,X3 :]"
  hence "x in [:[:X1,X2:],X3:]" using zfmisc_1_def_3 all_set by auto
  then obtain x12 x3 where
   A1:  "x12 be object" "x3 be object" "x12 in [:X1,X2:] \<and> x3 in X3 \<and> x = [x12,x3]" using zfmisc_1_def_2 by infer_auto
  obtain x1 x2 where
     "x1 be object" "x2 be object" "x1 in X1 \<and> x2 in X2 \<and> x12 = [x1,x2]" using A1 zfmisc_1_def_2 by infer_auto
  thus "ex x1,x2,x3 be object st x = [x1,x2,x3] \<and> x1 in X1 \<and> x2 in X2 \<and> x3 in X3" using A1 by auto
qed

mtheorem zfmisc_th_4:
  "x in [:[:X1,X2:] , [:X3,X4:]:] \<Longrightarrow> ex x1,x2,x3,x4 be object st 
       x = [[x1,x2],[x3,x4]] \<and> x1 in X1 \<and> x2 in X2 \<and> x3 in X3 \<and> x4 in X4"
proof-
  assume "x in [:[:X1,X2:] , [:X3,X4:]:]"
   then obtain x12 x34 where
    "x12 be object" "x34 be object" and A1:
    "x12 in [:X1,X2:] \<and> x34 in [:X3,X4:] \<and> x = [x12,x34]" using zfmisc_1_def_2 by infer_auto
  then obtain x1 x2 where
    "x1 be object" "x2 be object" and A2:
    "x1 in X1 \<and> x2 in X2 \<and> x12 = [x1,x2]" using zfmisc_1_def_2 by infer_auto
  obtain x3 x4 where
    "x3 be object" "x4 be object" and A3:
    "x3 in X3 \<and> x4 in X4 \<and> x34 = [x3,x4]" using zfmisc_1_def_2 A1 by infer_auto
  show " ex x1,x2,x3,x4 be object st 
       x = [[x1,x2],[x3,x4]] \<and> x1 in X1 \<and> x2 in X2 \<and> x3 in X3 \<and> x4 in X4"
    using A1 A2 A3 by infer_auto
qed

mdef zfmisc_1_def_10 ("trivial")where
  "attr trivial for set means (\<lambda>X. for x,y st x in X \<and> y in X holds x=y)"..


mtheorem
  mlet "x be object"
  "cluster {x} \<rightarrow> trivial" using zfmisc_1_def_10I tarski_def_1 by infer_auto

   
mtheorem zfmisc_1_th_28:
  "[:{x},{y}:] = {[x,y]}"
proof
  show "[:{x},{y}:] be set" "{[x,y]} be set" by infer_auto
  fix z
  show "z in [:{x},{y}:] \<longleftrightarrow> z in {[x,y]}"
    proof (rule iffI3)
      show "z in [:{x},{y}:] \<longrightarrow> z in {[x,y]}"
        proof
          assume "z in [:{x},{y}:]"
          then obtain x1 y1 where
            "x1 be object" "y1 be object" and
            A1:"x1 in {x} \<and> y1 in {y}" and
            A2:"z=[x1,y1]" using zfmisc_1_def_2 by infer_auto
          have "x1=x \<and> y1=y" using A1 tarski_def_1 by simp
          thus "z in {[x,y]}" using A2 tarski_def_1 by simp
       qed
        assume "z in {[x,y]}"
        hence A3: "z=[x,y]" using tarski_def_1 by simp
        have "x in {x} \<and> y in {y}" using tarski_def_1 by simp
        thus "z in [:{x},{y}:]" using A3 zfmisc_1_def_2 tarski_def_1 by infer_simp
     qed
qed

mtheorem zfmisc_1_th_33:
 "Y c= { x } iff Y = {} or Y = { x }"
proof(rule iffI3)
  show "Y c= { x } implies Y = {} or Y = { x }"
  proof
    assume A1: "Y c= { x }"
    have "Y<>{} implies Y={x}"
    proof
      assume "Y <>{}"
      hence "Y is non empty" using xboole_0_lm_1[of Y] xboole_0_def_1 by infer_auto 
      then obtain y where
        A2: "y in Y" using xboole_0_def_1 by infer_auto
      hence "y in {x}" using A1 tarski_def_3E[of Y "{x}"] by infer_auto
      hence A3: "y=x" using tarski_def_1 by auto
      have "{x} c= Y"
      proof(standard,auto)
        fix z assume "z in {x}"
        hence "z=x" using tarski_def_1 by auto
        thus "z in Y" using A2 A3 by simp
      qed infer_auto
      thus "Y={x}" using A1 xboole_0_def_10 by infer_auto  
    qed
    thus "Y = {} or Y = { x }" by auto
 qed
next 
  assume " Y = {} or Y = { x }"
  thus "Y c= {x}" using xboole_0_def_10 tarski_def_3 xb by infer_auto
qed

mtheorem zfmisc_1_th_87:
  "for x,y holds [x,y] in [:X,Y:] \<longleftrightarrow> x in X \<and> y in Y"
proof (intro ballI)
  fix x y
  assume T0: "x be object" "y be object"
  show "[x,y] in [:X,Y:] \<longleftrightarrow> x in X \<and> y in Y"
     proof(rule iffI2)
        show "[x,y] in [:X,Y:] \<longrightarrow> x in X \<and> y in Y"
           proof
               assume "[x,y] in [:X,Y:]"
               hence "ex x1,y1 st x1 in X \<and> y1 in Y \<and> [x,y]=[x1,y1]" using zfmisc_1_def_2 ty by auto
               then obtain x1 y1 where
                  "x1 be object "  "y1 be object " and A1: "x1 in X \<and> y1 in Y \<and> [x,y]=[x1,y1]" by auto
               have "x=x1 \<and> y=y1" using A1 xtuple_0_th_1a by auto
               thus "x in X \<and> y in Y" using A1 by simp
           qed
       show "x in X \<and> y in Y \<longrightarrow> [x,y] in [:X,Y:]" using zfmisc_1_def_2 by infer_auto
    qed
  qed simp_all

mtheorem zfmisc_1_cl_1:
  mlet "X be non empty\<bar>set", "Y be non empty\<bar>set"  
  "cluster [:X,Y:] \<rightarrow> non empty"
proof
  obtain x where
     X: "x in X" using xboole_0_def_1[of X] by infer_auto
  obtain y where
     Y: "y in Y" using xboole_0_def_1[of Y] by infer_auto
  have "[x,y] in [:X,Y:]" using zfmisc_1_th_87 X Y by infer_auto
  then show "[:X,Y:] is non empty" using xboole_0_def_1 by infer_auto
qed

reserve X1, X2,Y1,Y2 for set

mtheorem zfmisc_1_th_96:
  "X1 \<subseteq> Y1 \<and> X2 \<subseteq> Y2 \<longrightarrow> [:X1,X2:] \<subseteq> [:Y1,Y2:]"
proof
  assume A1: "X1 \<subseteq> Y1 \<and> X2 \<subseteq> Y2"
  show "[:X1,X2:] \<subseteq> [:Y1,Y2:]"
  proof(standard,auto)
       fix x
       assume A2: "x in [:X1,X2:]"
       then obtain x1 x2 where
        T0: "x1 be object" "x2 be object" and A3: "x = [x1,x2]" using zfmisc_1_def_2 by infer_auto
       have "x1 in X1" "x2 in X2" using A2 A3 zfmisc_1_th_87 by infer_auto
       hence "x1 in Y1" "x2 in Y2" using A1 tarski_def_3E[of X1 Y1] tarski_def_3E[of X2 Y2] by infer_auto
       thus "x in [:Y1,Y2:]" using A3 zfmisc_1_th_87 by infer_simp
    qed infer_auto
  qed

text_raw {*\DefineSnippet{zfmisc_1_th_112}{*}
reserve X,Y,N,M for set
mtheorem zfmisc_1_th_112:
  "\<exists>M. N in M \<and> (\<forall>X,Y. X in M \<and> Y \<subseteq> X \<longrightarrow> Y in M) \<and>
    (\<forall>X. X in M \<longrightarrow> bool X in M) \<and>
    (\<forall>X. X \<subseteq> M \<longrightarrow> X,M areequipotent \<or> X in M)"
text_raw {*}%EndSnippet*}
proof-
  obtain M where
    [ty]: "M is set" and
    A1: "N in M" and
    A2: "\<forall>X : set. \<forall>Y : set. X in M \<and> Y \<subseteq> X \<longrightarrow> Y in M" and
    A3: "\<forall>X : set. X in M \<longrightarrow> (\<exists>Z : set. Z in M \<and> (\<forall>Y : set. Y \<subseteq> X \<longrightarrow> Y in Z))" and
    A4: "\<forall>X : set. X \<subseteq> M \<longrightarrow> X,M areequipotent \<or> X in M"
    using tarski_a_th_1[THEN bspec,of N,simplified] all_set by auto
  show ?thesis
  proof (intro bexI conjI)
    show "N in M" using A1 .
    show "\<forall>X : set. \<forall>Y : set. X in M \<and> Y \<subseteq> X \<longrightarrow> Y in M" using A2 .
    show "\<forall>X : set. X in M \<longrightarrow> bool X in M"
    proof (intro ballI impI)
      fix X
      assume [ty]: "X is set"
      assume "X in M"
      then obtain Z where
        [ty]: "Z be set" and
        A5: "Z in M" and
        A6: "for Y st Y c= X holds Y in Z" using A3[THEN bspec,of X] by infer_auto
      {
        fix Y
        have [ty]: "Y is set" using all_set .
        assume "Y in bool X"
        hence "Y c= X" using zfmisc_1_def_1 by infer_auto
        hence "Y in Z" using A6 by infer_auto
      }
      thus "bool X in M"
        using
        A2[THEN bspec,THEN bspec,simplified,rule_format,OF all_set,where ?x="bool X"]
        A5
        tarski_def_3I
        by infer_auto
    qed infer_auto
  show "\<forall>X : set. X \<subseteq> M \<longrightarrow> X,M areequipotent \<or> X in M" using A4 .
  qed infer_auto
qed


end
