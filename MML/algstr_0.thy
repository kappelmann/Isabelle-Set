theory algstr_0 
imports struct_0 funct_2
begin


mdef addMagma :: "Ty" ("addMagma") where
  "struct [1-sorted] addMagma(#carrier \<rightarrow> set';addF\<rightarrow> BinOp-of' the' carrier #)
   defined on {carrier}\<union>{addF}"
  by (auto simp add:one_sorted, 
      auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)  

mtheorem
  mlet "X be set", "B be BinOp-of X"
  "cluster [#carrier\<mapsto>X;addF \<mapsto> B#] \<rightarrow> strict(addMagma)"
 unfolding addMagma_def
    by (auto,rule struct_aggr_ancesors_rule,
         auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string) ty_auto

mtheorem 
  mlet "X be addMagma" 
  "cluster (the addF of X) \<rightarrow> BinOp-of (the carrier of X)" 
using field addMagmaE by ty_auto

mdef AddMagmaFixCarrier ("_-carrier addMagma") where
  mlet "C be set"
  "func C -carrier addMagma  \<rightarrow> set means
     (\<lambda>it. for x be object holds x in it iff x be strict(addMagma)& the carrier of x = C  )"  
proof-
  let ?F = "Funcs([:C,C:],C)"
  let ?P="\<lambda> x y. y = [#carrier\<mapsto>C;addF \<mapsto> x#]"
  have P: "\<forall>x,y,z:object. ?P(x,y) \<and> ?P(x,z) \<longrightarrow> y = z" by auto
  then obtain X where [ty]: "X be set" and
   X: "\<forall>x:object.
   x in X \<longleftrightarrow> (\<exists>y:object. y in ?F \<and> ?P(y,x))" using tarski_0_sch_1[of ?F ?P,OF _ P] by infer_auto

  show "ex x be set st for xa be object holds (xa in x \<longleftrightarrow> xa be strict(addMagma) & the carrier of xa = C)"
  proof(rule bexI[of _ X],standard,rule iffI3)
    fix  x  
    show "x in X \<longrightarrow> x be strict(addMagma) \<and> the carrier of x = C"
    proof
      assume "x in X"
      then obtain y where
        A1: "y in ?F & ?P(y,x)" using X by auto
      then obtain f where A2[ty]: "f be Function" and
         A3: " y = f \<and> dom f = [:C,C:] \<and> rng f c= C" using funct_2_def_2 by infer_auto
      hence [ty]: "f is BinOp-of C" using funct_2_th_3[of C f] by ty_auto
      have A4: "[#carrier\<mapsto>C;addF \<mapsto> f#] is strict(addMagma)" by infer_auto
      have "the carrier of [#carrier\<mapsto>C;addF \<mapsto> f#] = C"  using 
        the_selector_of_1[of _ "carrier"] aggr Struct_2 string by mauto
      then show "x be strict(addMagma) \<and> the carrier of x = C" using A1 A3 A4 by auto           
    qed
    have [ty]: "[:C,C:] is set" using all_set by auto
    assume A5: "x be strict(addMagma) \<and> the carrier of x = C"
    hence [ty]: "x be strict(addMagma)" by simp
    let ?B = "the addF of x"
    have [ty]: "?B is BinOp-of C" using A5 by infer_auto
    have [ty]: "?B be Function" by ty_auto
    have "dom ?B = [:C,C:]" "rng ?B c= C" using binop_1_mode_2[of C ?B] A5 relat_1_def_19E[of C ?B] by ty_auto
    hence B: "?B in ?F" using funct_2_def_2[of "[:C,C:]" C ?B] by ty_auto
    have "?P(?B,x)"
    proof(rule Equal_strict[of _ _ addMagma], ty_auto)
      let ?X = "[# carrier \<mapsto> C; addF \<mapsto> ?B #]"  
      fix sel assume B1: "sel in domain_of addMagma"
      hence S: "sel = carrier or sel = addF" using string addMagma_dom by auto
      have "the carrier of ?X=C" "the addF of ?X=?B" 
         using the_selector_of_1[of _ "carrier"]  the_selector_of_1[of _ "addF"] aggr by infer_auto  
      then show "the sel of x = the sel of ?X" using S A5 by auto      
    qed infer_auto
    then show "x in X" using B X by auto
  qed mauto
  fix IT1 IT2 assume [ty]: "IT1 be set" "IT2 be set" 

  assume A1: "for x being object holds (x in IT1 \<longleftrightarrow> x be strict(addMagma) \<and> the' carrier(x) = C)"
     and A2: "for x being object holds (x in IT2 \<longleftrightarrow> x be strict(addMagma) \<and> the' carrier(x) = C)"
  {
      fix x
      assume T1:"x be object"
      have "x in IT1 \<longleftrightarrow> x be strict(addMagma) \<and> the' carrier(x) = C" using A1 T1 by auto
      then have "x in IT1 \<longleftrightarrow> x in IT2" using A2 T1 by auto
  }
  thus "IT1 = IT2" by (intro tarski_th_2) ty_auto
qed mauto
   
mtheorem algstr_0_cl_1:
  mlet "D be non empty\<bar>set","o be BinOp-of D"
  "cluster [#carrier\<mapsto> D ; addF\<mapsto>o#] \<rightarrow> non empty-struct"
proof
  let ?X = "[#carrier\<mapsto> D ; addF\<mapsto>o#]"
  have T1[ty]: "?X be addMagma" by mauto
  have "the carrier of ?X = D" using aggr by (intro the_selector_of_1) ty_auto
  thus "?X is non empty-struct" using struct_0_def_1 addMagma one_sorted T1 by ty_auto
qed

mtheorem algstr_0_cl_2:
  mlet "T be trivial\<bar>set","f be BinOp-of T"
  "cluster [#carrier\<mapsto> T ; addF\<mapsto>f#] \<rightarrow> trivial-struct"
proof
  let ?X = "[#carrier\<mapsto> T ; addF\<mapsto>f#]"
  have T1[ty]: "?X be addMagma" by mauto
  hence T2: "the carrier of ?X = T" "?X be 1-sorted" using the_selector_of_1[of ?X carrier T] aggr by ty_auto
  show "?X is trivial-struct" using struct_0_def_9[of ?X] T2 by ty_auto
qed

mtheorem algstr_0_cl_3:
  mlet "N be non trivial\<bar>set", "b be BinOp-of N"
   "cluster [#carrier\<mapsto>N ; addF\<mapsto>b#] \<rightarrow> non trivial-struct"
proof
  let ?X = "[#carrier\<mapsto>N ; addF\<mapsto>b#]"
  have [ty]: "?X be addMagma" by mauto
  hence "the carrier of ?X = N" using the_selector_of_1[of ?X carrier N]  aggr by ty_auto
  thus "?X is non trivial-struct" using struct_0_def_9[of ?X] by ty_auto
qed

text_raw {*\DefineSnippet{algstr0def1}{*}

mdef algstr_0_def_1 ("_ \<oplus>\<^sub>_ _" [66,1000,67] 66) where
  mlet "M be addMagma", "x be Element-of-struct M",
       "y be Element-of-struct M"
  "func x \<oplus>\<^sub>M y \<rightarrow> Element-of-struct M equals
     (the addF of M) . \<lparr> x , y \<rparr>"
text_raw {*}%EndSnippet*}
proof-
  let ?A = "the carrier of M"
   have A1: "(the addF of M) be BinOp-of ?A" "?A be set" using ty by auto
   thus " (the addF of M) .  \<lparr> x , y \<rparr> be Element-of ?A"
          using binop_0_def_20A by ty_auto
qed

abbreviation algstr_0_def_2 ("Trivial-addMagma") where
  "Trivial-addMagma \<equiv> [# carrier\<mapsto>{{}} ; addF \<mapsto> op2 #]"

mtheorem algstr_0_cl_4:
  "cluster Trivial-addMagma \<rightarrow> 1-element-struct\<bar> strict (addMagma)"
proof (standard, ty_auto)
  let ?T ="Trivial-addMagma"
  have T0[ty]: "?T be addMagma" by mauto
  have T1: "the carrier of ?T={{}}"
    using the_selector_of_1[of ?T carrier "{{}}"] aggr by ty_auto
  thus "?T is 1-element-struct" using struct_0_def_19_a by ty_auto
qed

mtheorem algstr_0_cl_5:
  "cluster strict (addMagma)\<bar>1-element-struct for addMagma"
proof(standard,standard)
  show "Trivial-addMagma is strict (addMagma)\<bar>1-element-struct\<bar> addMagma" by infer_auto
qed


mdef algstr_0_def_3 ("left-add-cancelable\<^sub>_" [200] 200)where
 mlet  "M be addMagma"
"attr left-add-cancelable\<^sub>M for Element-of-struct M means
     (\<lambda> x. for y,z be Element-of-struct M st x \<oplus>\<^sub>M y = x \<oplus>\<^sub>M z holds y = z)".


mdef algstr_0_def_4 ("right-add-cancelable\<^sub>_" [200] 200)where  
mlet "M be addMagma"
 "attr right-add-cancelable\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       (for y,z be Element-of-struct M st y \<oplus>\<^sub>M x = z \<oplus>\<^sub>M x holds y = z))".

mdef algstr_0_def_5 ("add-cancelable\<^sub>_" [200] 200)where
  mlet "M be addMagma"
  " attr add-cancelable\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       x is right-add-cancelable\<^sub>M \<bar> left-add-cancelable\<^sub>M)".

mtheorem algstr_0_cl_6:
  mlet "M be addMagma"
  "cluster right-add-cancelable\<^sub>M \<bar> left-add-cancelable\<^sub>M \<rightarrow> add-cancelable\<^sub>M for Element-of-struct M" 
using algstr_0_def_5 by ty_auto

mtheorem algstr_0_cl_7:
  mlet "M be addMagma"
  "cluster add-cancelable\<^sub>M \<rightarrow> right-add-cancelable\<^sub>M \<bar> left-add-cancelable\<^sub>M for Element-of-struct M" 
using algstr_0_def_5 by ty_auto

mdef algstr_0_def_6 ("left-add-cancelable")where
   "attr left-add-cancelable for addMagma means (\<lambda> M.  (for x be Element-of-struct M holds x is left-add-cancelable\<^sub>M))".

mdef algstr_0_def_7 ("right-add-cancelable")where
   "attr right-add-cancelable for addMagma means (\<lambda> M.
                                       (for x be Element-of-struct M holds x is right-add-cancelable\<^sub>M))".

mdef algstr_0_def_8 ("add-cancelable")where
   "attr add-cancelable for addMagma means (\<lambda> M.
                                       M is right-add-cancelable \<bar> left-add-cancelable)".

mtheorem algstr_0_cl_8:
  "cluster right-add-cancelable \<bar> left-add-cancelable \<rightarrow> add-cancelable for addMagma" 
 using algstr_0_def_8 by auto


mtheorem algstr_0_cl_9:
  "cluster add-cancelable \<rightarrow> right-add-cancelable \<bar> left-add-cancelable for addMagma" 
using algstr_0_def_8 by auto

mtheorem algstr_0_cl_10:
  "cluster Trivial-addMagma \<rightarrow> add-cancelable"
proof(standard,standard,auto)
  let ?T ="Trivial-addMagma"
  have [ty]: "?T be addMagma" by mauto
  have T1: "the carrier of ?T={{}}"
    using aggr the_selector_of_1 by ty_auto
  show "?T is right-add-cancelable"
    proof(standard,auto)
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is right-add-cancelable\<^sub>?T"
      proof(standard,auto)
        fix y z assume T3[ty]: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "y \<oplus>\<^sub>?T x = z \<oplus>\<^sub>?T x"
        show "y = z" using struct_0_def_10[THEN iffD1,THEN bspec,THEN bspec,of ?T y z] by ty_auto
      qed ty_auto
    qed mauto
  show "?T is left-add-cancelable"
    proof(standard,auto)
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is left-add-cancelable\<^sub>?T"
      proof(standard,auto)
        fix y z assume T3[ty]: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "x \<oplus>\<^sub>?T y = x \<oplus>\<^sub>?T z"
        show "y = z" using struct_0_def_10[THEN iffD1,THEN bspec,THEN bspec,of ?T y z] by ty_auto
      qed ty_auto
    qed mauto
qed mauto

mtheorem algstr_0_cl_11:
  "cluster add-cancelable\<bar>strict (addMagma)\<bar>1-element-struct for addMagma"
proof(standard,standard,simp,intro conjI)
  show "Trivial-addMagma is add-cancelable "
        "Trivial-addMagma is strict (addMagma)"
        "Trivial-addMagma is 1-element-struct"
        "Trivial-addMagma be addMagma" by infer_auto
qed

mtheorem algstr_0_cl_12:
  mlet "M be left-add-cancelable \<bar> addMagma"
  "cluster \<rightarrow> left-add-cancelable\<^sub>M for Element-of-struct M"
proof(standard,standard)
  fix X assume T[ty]: "X be Element-of-struct M"
  show "X be left-add-cancelable\<^sub>M" using algstr_0_def_6E[THEN bspec,of M X] by mauto
qed mauto

mtheorem algstr_0_cl_13:
  mlet "M be right-add-cancelable \<bar> addMagma"
  "cluster \<rightarrow> right-add-cancelable\<^sub>M for Element-of-struct M"
proof(standard,standard)
  fix X assume T[ty]: "X be Element-of-struct M"
  show "X be right-add-cancelable\<^sub>M" using algstr_0_def_7E[of M] by ty_auto
qed mauto

mdef addLoopStr ("addLoopStr") where
"struct [addMagma\<bar>ZeroStr]addLoopStr
  (# carrier \<rightarrow> set';
     addF \<rightarrow> BinOp-of' the' carrier;
     ZeroF \<rightarrow> Element-of' the' carrier #) defined on {carrier}\<union>{addF}\<union>{ZeroF}"
 by (auto simp add:addMagma ZeroStr,
     auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)    

mtheorem
   mlet "X be set","B be BinOp-of X","E be Element-of X"
   "cluster [#carrier \<mapsto> X ; addF\<mapsto>B ; ZeroF\<mapsto>E#] \<rightarrow> strict(addLoopStr)"
unfolding addLoopStr_def
    by (auto,rule struct_aggr_ancesors_rule,
         auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string) ty_auto


mtheorem algstr_0_cl_14:
  mlet "D be non empty\<bar>set "," o be BinOp-of D "," d be Element-of D"
  " cluster [#carrier \<mapsto> D ; addF\<mapsto>o ; ZeroF\<mapsto>d#] \<rightarrow> non empty-struct"
proof
  let ?X = "[#carrier \<mapsto> D ; addF\<mapsto>o ; ZeroF\<mapsto>d#]"
  have T1[ty]: "?X be addLoopStr" by mauto
  have "the carrier of ?X = D" using the_selector_of_1[of ?X carrier D] aggr by ty_auto
  thus "?X is non empty-struct" using struct_0_def_1 by ty_auto
qed

mtheorem algstr_0_cl_15:
  mlet "T be trivial\<bar>set", "f be BinOp-of T","t be Element-of T"
   "cluster [#carrier\<mapsto>T;addF\<mapsto>f;ZeroF\<mapsto>t#] \<rightarrow> trivial-struct"
proof
  let ?X = "[#carrier\<mapsto>T;addF\<mapsto>f;ZeroF\<mapsto>t#]"
  have T1[ty]: "?X be addLoopStr" by mauto
  have T2: "the carrier of ?X = T" using the_selector_of_1[of ?X carrier T] aggr by ty_auto
  show "?X is trivial-struct" using struct_0_def_9[of ?X,rule_format] T2(1) by ty_auto
qed

mtheorem algstr_0_cl_16:
  mlet "N be non trivial\<bar>set","b be BinOp-of N","m be Element-of N"
  "cluster [#carrier \<mapsto> N ; addF\<mapsto>b ; ZeroF\<mapsto>m#] \<rightarrow> non trivial-struct"
proof
  let ?X = "[#carrier \<mapsto> N ; addF\<mapsto>b ; ZeroF\<mapsto>m#]"
  have T1[ty]: "?X be addLoopStr" by mauto
  hence "the carrier of ?X = N" using the_selector_of_1[of ?X carrier N] aggr by ty_auto
  thus "?X is non trivial-struct" using struct_0_def_9 by ty_auto
qed

abbreviation algstr_0_def_9 ("Trivial-addLoopStr") where
   "Trivial-addLoopStr \<equiv>
     [# Trivial-addMagma; ZeroF \<mapsto> {} #]"

mtheorem algstr_0_cl_17:
  "cluster Trivial-addLoopStr \<rightarrow> 1-element-struct\<bar> strict (addLoopStr)"
proof(standard,auto)
  let ?T ="Trivial-addLoopStr"
  have T0[ty]: "?T be addLoopStr" by mauto
  have T1: "the carrier of ?T={{}}"
    using the_selector_of_1[of ?T carrier "{{}}"] using aggr by ty_auto
  thus T2: "?T is 1-element-struct" using T0 struct_0_def_19_a by ty_auto
qed ty_auto

mtheorem algstr_0_cl_18:
  "cluster strict (addLoopStr)\<bar>1-element-struct for addLoopStr"
proof(standard,standard)
  show "Trivial-addLoopStr is strict (addLoopStr)\<bar> 1-element-struct \<bar> addLoopStr" 
    by infer_auto
qed

mdef algstr_0_def_10 ("left-complementable\<^sub>_" [200] 200)where
mlet   "M be addLoopStr "
" attr left-complementable\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       (ex y be Element-of-struct M st y \<oplus>\<^sub>M x =0\<^sub>M))".

mdef algstr_0_def_11 ("right-complementable\<^sub>_" [200] 200)where
 mlet  "M be addLoopStr "
 " attr right-complementable\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       (ex y be Element-of-struct M st x \<oplus>\<^sub>M y =0\<^sub>M))".
text_raw {*\DefineSnippet{algstr_0_def_12}{*}
mdef algstr_0_def_12 ("add-complementable\<^sub>_" [200] 200)where
mlet    " M be addLoopStr""attr add-complementable\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       x is right-complementable\<^sub>M \<bar> left-complementable\<^sub>M)".
text_raw {*}%EndSnippet*}


text_raw {*\DefineSnippet{algstr_0_cl_19}{*}
mtheorem algstr_0_cl_19:
  mlet "M be addLoopStr"
   "cluster right-complementable\<^sub>M \<bar> left-complementable\<^sub>M \<rightarrow> add-complementable\<^sub>M for Element-of-struct M"
using algstr_0_def_12I by ty_auto
text_raw {*}%EndSnippet*}


text_raw {*\DefineSnippet{algstr_0_cl_20}{*}
mtheorem algstr_0_cl_20:
  mlet "M be addLoopStr"
   "cluster add-complementable\<^sub>M \<rightarrow> right-complementable\<^sub>M \<bar> left-complementable\<^sub>M for Element-of-struct M"
using algstr_0_def_12E by ty_auto
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{algstr0def13}{*}

mdef algstr_0_def_13 ("\<ominus>\<^sub>_ _" [1000, 86] 87) where
 mlet "M be addLoopStr",
          "x be Element-of-struct M"
  "assume x is left-complementable\<^sub>M \<bar> right-add-cancelable\<^sub>M
   func \<ominus>\<^sub>M x \<rightarrow> Element-of-struct M means
     (\<lambda>it. it \<oplus>\<^sub>M x = 0\<^sub>M)"
text_raw {*}%EndSnippet*}
proof-
      assume [ty]:"x is left-complementable\<^sub>M \<bar>right-add-cancelable\<^sub>M"
      thus "ex y be Element-of-struct M st y \<oplus>\<^sub>M x= 0\<^sub>M" using algstr_0_def_10 by mauto
  next
     assume A1[ty]: "x is left-complementable\<^sub>M \<bar>right-add-cancelable\<^sub>M"
     fix y1 y2

     assume T0[ty]: "y1 be Element-of-struct M"
                "y2 be Element-of-struct M"
     assume A2: " y1 \<oplus>\<^sub>M x= 0\<^sub>M" and
    A3: " y2 \<oplus>\<^sub>M x= 0\<^sub>M"
     thus "y1=y2" using algstr_0_def_4E[of M x,THEN bspec,THEN bspec] by mauto
  next
     show "inhabited( Element-of-struct M)" by auto
qed


mdef algstr_0_def_14 ("_ \<ominus>\<^sub>_ _" [66,1000, 67] 66) where
  mlet "M be addLoopStr","x be Element-of-struct M","y be Element-of-struct M"
  "func x \<ominus>\<^sub>M y \<rightarrow> Element-of-struct M equals
     x \<oplus>\<^sub>M \<ominus>\<^sub>M y"
proof-
   show "(x \<oplus>\<^sub>M \<ominus>\<^sub>M y) be Element-of-struct M" using algstr_0_def_1[of M x "\<ominus>\<^sub>M y"] by mauto
qed

mtheorem algstr_0_cl_21:
  "cluster Trivial-addLoopStr \<rightarrow> add-cancelable"
proof(standard,standard,auto, infer_ty)
  let ?T ="Trivial-addLoopStr"
  have [ty]:"?T be addLoopStr" by ty_auto
       have T1: "the carrier of ?T={{}}"
      using aggr the_selector_of_1 by ty_auto
      show "?T is right-add-cancelable"
    proof(standard,auto)
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is right-add-cancelable\<^sub>?T"
      proof(standard,auto)
        fix y z assume T3[ty]: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "y \<oplus>\<^sub>?T x = z \<oplus>\<^sub>?T x"
        show "y = z" using struct_0_def_10E[THEN bspec,THEN bspec,of ?T y z] by ty_auto
      qed ty_auto
    qed mauto
  show "?T is left-add-cancelable"
    proof(standard,auto)
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is left-add-cancelable\<^sub>?T"
      proof(standard,auto)
        fix y z assume T3[ty]: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "x \<oplus>\<^sub>?T y = x \<oplus>\<^sub>?T z"
        show "y = z" using struct_0_def_10E[THEN bspec,THEN bspec,of ?T y z] by ty_auto
      qed ty_auto
    qed ty_auto
 qed ty_auto

mdef algstr_0_def_15 ("left-complementable")where
   "attr left-complementable for addLoopStr means (\<lambda> M. (for x be Element-of-struct M holds x is left-complementable\<^sub>M))".


mdef algstr_0_def_16 ("right-complementable")where
   "attr right-complementable for addLoopStr means (\<lambda> M.
                                       (for x be Element-of-struct M holds x is right-complementable\<^sub>M))".

mdef algstr_0_def_17 ("complementable")where
   "attr complementable for addLoopStr means (\<lambda> M.
                                       M is right-complementable \<bar> left-complementable)".

mtheorem algstr_0_cl_22:
  "cluster right-complementable \<bar> left-complementable \<rightarrow> complementable for addLoopStr" 
using algstr_0_def_17 by auto

mtheorem algstr_0_cl_23:
  "cluster complementable \<rightarrow> right-complementable \<bar> left-complementable for addLoopStr" 
 using algstr_0_def_17 by auto

mtheorem algstr_0_cl_24:
  "cluster Trivial-addLoopStr \<rightarrow> complementable"
proof(standard,standard,auto)
  let ?T ="Trivial-addLoopStr"
  have [ty]:"?T be addLoopStr" by ty_auto
  have T1: "the carrier of ?T={{}}"
    using aggr the_selector_of_1 by ty_auto

  show "?T is right-complementable"
    proof(standard,auto)
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is right-complementable\<^sub>?T"
      proof
        show "x be Element-of-struct ?T" using T2 by simp
        have "x \<oplus>\<^sub>?T x = 0\<^sub>?T" using struct_0_def_10E[THEN bspec,THEN bspec,of ?T "x \<oplus>\<^sub>?T x" "0\<^sub>?T"] by infer_auto
        thus "ex y be Element-of-struct ?T st x \<oplus>\<^sub>?T y = 0\<^sub>?T" using bexI[of _ x] by mauto
      qed ty_auto
    qed mauto
  show "?T is left-complementable"
    proof(standard,auto)
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is left-complementable\<^sub>?T"
      proof
        show "x be Element-of-struct ?T" using T2 by simp
        have "x \<oplus>\<^sub>?T x =0\<^sub>?T"  using struct_0_def_10E[THEN bspec,THEN bspec,of ?T "x \<oplus>\<^sub>?T x" "0\<^sub>?T"] by infer_auto
        thus "ex y be Element-of-struct ?T st y \<oplus>\<^sub>?T x = 0\<^sub>?T" using bexI[of _ x] by mauto
      qed ty_auto
    qed mauto
  qed mauto

mtheorem algstr_0_cl_25:
  "cluster complementable\<bar>add-cancelable\<bar>strict (addLoopStr)\<bar>1-element-struct for addLoopStr"
proof(standard,standard)
  show "Trivial-addLoopStr be complementable \<bar> add-cancelable \<bar> strict(addLoopStr) \<bar> 1-element-struct \<bar> addLoopStr"
    by mauto
qed



mtheorem algstr_0_cl_26:
  mlet "M be left-complementable \<bar> addLoopStr"
  "cluster \<rightarrow> left-complementable\<^sub>M for Element-of-struct M"
proof(standard,standard)
  fix X
  assume [ty]: "X is Element-of-struct M"
  thus "X is left-complementable\<^sub>M" using algstr_0_def_15E[of M] by mauto
qed mauto


mtheorem algstr_0_cl_27:
  mlet "M be right-complementable \<bar> addLoopStr"
  "cluster \<rightarrow> right-complementable\<^sub>M for Element-of-struct M"
proof(standard,standard)
  fix X
  assume [ty]: "X is Element-of-struct M"
  thus "X is right-complementable\<^sub>M" using algstr_0_def_16E[of M] by mauto
qed mauto

section "Multiplicative structures"

abbreviation "multMagma_fields \<equiv> (#carrier \<rightarrow> set';multF\<rightarrow> BinOp-of' the' carrier #)"

text_raw {*\DefineSnippet{multMagma}{*}
mdef multMagma ("multMagma") where
  "struct [1-sorted] multMagma (#
  carrier \<rightarrow> set';
  multF\<rightarrow> BinOp-of' the' carrier #) defined on {carrier}\<union>{multF}"
text_raw {*}%EndSnippet*}
  by (auto simp add:one_sorted,
     auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

mtheorem
   mlet "X be set","M be BinOp-of X"
   "cluster [#carrier \<mapsto> X ; multF\<mapsto>M #] \<rightarrow> strict(multMagma)"
unfolding multMagma_def
    by (auto,rule struct_aggr_ancesors_rule,
         auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string) ty_auto

mtheorem
  mlet "X be multMagma" 
  "cluster (the multF of X) \<rightarrow> BinOp-of (the carrier of X)" 
  using field multMagmaE by ty_auto

mtheorem algstr_0_cl_28:
  mlet "D be non empty\<bar>set","o be BinOp-of D"
  "cluster [#carrier\<mapsto>D;multF\<mapsto>o#] \<rightarrow> non empty-struct"
proof
  let ?X = "[#carrier\<mapsto>D;multF\<mapsto>o#]"
  have [ty]: "?X be multMagma" by mauto
  have "the carrier of ?X = D" using the_selector_of_1[of ?X carrier D] aggr by ty_auto
  thus "?X is non empty-struct" using struct_0_def_1 by ty_auto
qed

mtheorem algstr_0_cl_29:
  mlet "T be trivial\<bar>set","f be BinOp-of T"
   "cluster [#carrier\<mapsto>T;multF\<mapsto>f#] \<rightarrow> trivial-struct"
proof
  let ?X = "[#carrier\<mapsto>T;multF\<mapsto>f#]"
  have T2: "the carrier of ?X = T" "?X be 1-sorted" using the_selector_of_1[of ?X carrier T] aggr by mauto
  thus "?X is trivial-struct" using struct_0_def_9 by ty_auto
qed

mtheorem algstr_0_cl_30:
  mlet "N be non trivial\<bar>set","b be BinOp-of N"
  "cluster [#carrier\<mapsto>N;multF\<mapsto>b#] \<rightarrow> non trivial-struct"
proof
  let ?X = "[#carrier\<mapsto>N;multF\<mapsto>b#]"
  have T1[ty]: "?X be multMagma" by mauto
  hence T2: "the carrier of ?X = N" using the_selector_of_1[of ?X carrier N] aggr by ty_auto
  show "?X is non trivial-struct" using struct_0_def_9[of ?X] T2(1) by ty_auto
qed

text_raw {*\DefineSnippet{algstr0def18}{*}
mdef algstr_0_def_18 ("_ \<otimes>\<^sub>_ _" [96, 1000, 97] 96) where
mlet "M be multMagma "," x be Element-of-struct M","
         y be Element-of-struct M"
  "func x \<otimes>\<^sub>M y \<rightarrow> Element-of-struct M equals
     (the multF of M) . \<lparr> x , y \<rparr>"
text_raw {*}%EndSnippet*}
proof-
   let ?A = "the carrier of M"
   have A1: "(the multF of M) be BinOp-of ?A" "?A be set" by mauto
   thus " (the multF of M) .  \<lparr> x , y \<rparr> be Element-of ?A"
           using binop_0_def_20A by ty_auto
qed

abbreviation algstr_0_def_19 ("Trivial-multMagma") where
  "Trivial-multMagma \<equiv> [#carrier\<mapsto>{{}};multF\<mapsto>op2#]"

mtheorem algstr_0_cl_31:
  "cluster Trivial-multMagma \<rightarrow> 1-element-struct\<bar> strict (multMagma)"
proof(standard,auto)
  let ?T ="Trivial-multMagma"
  have T1: "the carrier of ?T={{}}"
    using the_selector_of_1[of ?T carrier "{{}}"] using aggr by mauto
  thus T2: "Trivial-multMagma is 1-element-struct" using struct_0_def_19_a by ty_auto
qed ty_auto

mtheorem algstr_0_cl_32:
  "cluster strict (multMagma)\<bar>1-element-struct for multMagma"
proof(standard,standard)
  show "Trivial-multMagma is strict(multMagma) \<bar> 1-element-struct \<bar> multMagma" by mauto
qed

mdef algstr_0_def_20 ("left-mult-cancelable\<^sub>_" [200] 200)where
mlet   "M be multMagma""attr left-mult-cancelable\<^sub>M for Element-of-struct M means
(\<lambda> x.
                                       (for y,z be Element-of-struct M st x \<otimes>\<^sub>M y = x \<otimes>\<^sub>M z holds y = z))".


mdef algstr_0_def_21 ("right-mult-cancelable\<^sub>_" [200] 200)where
mlet   " M be multMagma""attr right-mult-cancelable\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       (for y,z be Element-of-struct M st y \<otimes>\<^sub>M x = z \<otimes>\<^sub>M x holds y = z))".

mdef algstr_0_def_22 ("mult-cancelable\<^sub>_" [200] 200)where
mlet   " M be multMagma" 
"attr mult-cancelable\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       x is right-mult-cancelable\<^sub>M \<bar> left-mult-cancelable\<^sub>M)".

mtheorem algstr_0_cl_33:
  mlet "M be multMagma"
   "cluster right-mult-cancelable\<^sub>M \<bar> left-mult-cancelable\<^sub>M \<rightarrow> mult-cancelable\<^sub>M for Element-of-struct M" 
using algstr_0_def_22 by ty_auto
  
mtheorem algstr_0_cl_34:
  mlet "M be multMagma"
  "cluster mult-cancelable\<^sub>M \<rightarrow> right-mult-cancelable\<^sub>M \<bar> left-mult-cancelable\<^sub>M for Element-of-struct M" 
using algstr_0_def_22 by ty_auto

mdef algstr_0_def_23 ("left-mult-cancelable")where
   "attr left-mult-cancelable for multMagma means (\<lambda> M.  (for x be Element-of-struct M holds x is left-mult-cancelable\<^sub>M))".

mdef algstr_0_def_24 ("right-mult-cancelable")where
   "attr right-mult-cancelable for multMagma means (\<lambda> M.
                                       (for x be Element-of-struct M holds x is right-mult-cancelable\<^sub>M))".

mdef algstr_0_def_25 ("mult-cancelable")where
   "attr mult-cancelable for multMagma means (\<lambda>M.
                                       M is right-mult-cancelable \<bar> left-mult-cancelable)".

mtheorem algstr_0_cl_35:
  "cluster right-mult-cancelable \<bar> left-mult-cancelable \<rightarrow> mult-cancelable for multMagma" 
using algstr_0_def_25 by auto
  
mtheorem algstr_0_cl_36:
  "cluster mult-cancelable \<rightarrow> right-mult-cancelable \<bar> left-mult-cancelable for multMagma" 
using algstr_0_def_25 by auto
    
mtheorem algstr_0_cl_37:
  "cluster Trivial-multMagma \<rightarrow> mult-cancelable"
proof(standard,standard,auto)
  let ?T ="Trivial-multMagma"
  have [ty]: "?T be multMagma" by ty_auto
  have T1: "the carrier of ?T={{}}"
    using aggr the_selector_of_1 by ty_auto
  show "?T is right-mult-cancelable"
    proof(standard,auto)
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is right-mult-cancelable\<^sub>?T"
      proof(standard,auto)
        fix y z assume T3[ty]: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "y \<otimes>\<^sub>?T x = z \<otimes>\<^sub>?T x"
        show "y = z" using struct_0_def_10E[THEN bspec,THEN bspec,of ?T y z] by mauto
      qed ty_auto
    qed mauto
  show "?T is left-mult-cancelable"
    proof(standard,auto)
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is left-mult-cancelable\<^sub>?T"
      proof(standard,auto)
        fix y z assume T3[ty]: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "x \<otimes>\<^sub>?T y = x \<otimes>\<^sub>?T z"
        show "y = z"  using struct_0_def_10E[THEN bspec,THEN bspec,of ?T y z] by ty_auto
      qed ty_auto
    qed mauto
qed mauto


mtheorem algstr_0_cl_38:
  "cluster mult-cancelable\<bar>strict (multMagma)\<bar>1-element-struct for multMagma"
proof(standard,standard)
  show "Trivial-multMagma is mult-cancelable\<bar>strict (multMagma)\<bar>1-element-struct\<bar>multMagma"
     by mauto
qed


mtheorem algstr_0_cl_39:
  mlet "M be left-mult-cancelable \<bar> multMagma"
  "cluster \<rightarrow> left-mult-cancelable\<^sub>M for Element-of-struct M"
proof(standard,standard)
  fix X assume [ty]:"X be Element-of-struct M"
  show "X be left-mult-cancelable\<^sub>M"
        using algstr_0_def_23E[of M] by ty_auto
qed mauto

mtheorem algstr_0_cl_40:
  mlet "M be right-mult-cancelable \<bar> multMagma"
  "cluster \<rightarrow> right-mult-cancelable\<^sub>M for Element-of-struct M"
proof (standard,standard)
  fix X assume [ty]:"X be Element-of-struct M"
  show "X be right-mult-cancelable\<^sub>M"
        using algstr_0_def_24E[of M ] by ty_auto
qed mauto

abbreviation "multLoopStr_fields \<equiv> (#carrier \<rightarrow> set'; OneF \<rightarrow> Element-of' the' carrier; multF\<rightarrow> BinOp-of' the' carrier #)"

mdef multLoopStr("multLoopStr") where
  "struct [multMagma \<bar> OneStr] multLoopStr 
      (#carrier \<rightarrow> set';multF\<rightarrow> BinOp-of' the' carrier; OneF \<rightarrow> Element-of' the' carrier #)
  defined on {carrier}\<union>{multF}\<union>{OneF}"
  by (auto simp add: multMagma OneStr,
     auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

mtheorem
  mlet "X be set","B be BinOp-of X","E be Element-of X"
  "cluster [#carrier\<mapsto>X ; multF\<mapsto> B;OneF\<mapsto>E #] \<rightarrow> strict(multLoopStr)"
unfolding multLoopStr_def
    by (auto,rule struct_aggr_ancesors_rule, 
        auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string) ty_auto

mtheorem algstr_0_cl_41:
  mlet "D be non empty\<bar>set","o be BinOp-of D","d be Element-of D"
  "cluster [#carrier\<mapsto>D ; multF\<mapsto> o;OneF\<mapsto>d#] \<rightarrow> non empty-struct"
proof(standard)
  let ?X = "[#carrier\<mapsto>D ; multF\<mapsto> o;OneF\<mapsto>d#]"
  have T1[ty]:"?X be multLoopStr" by mauto
  have "the carrier of ?X = D" using the_selector_of_1[of ?X carrier D]  aggr by ty_auto
  thus "?X is non empty-struct" using struct_0_def_1 by ty_simp
qed

mtheorem algstr_0_cl_42:
  mlet "T be trivial\<bar>set","f be BinOp-of T","t be Element-of T"
   "cluster [#carrier\<mapsto>T ; multF\<mapsto> f;OneF\<mapsto>t#] \<rightarrow> trivial-struct"
proof(standard)
  let ?X = "[#carrier\<mapsto>T ; multF\<mapsto> f;OneF\<mapsto>t#]"
  have T2: "the carrier of ?X = T" "?X be 1-sorted" using the_selector_of_1[of ?X carrier T]
    aggr by ty_auto
  thus "?X is trivial-struct" using struct_0_def_9[of ?X] by ty_auto
qed

mtheorem algstr_0_cl_43:
  mlet "N be non trivial\<bar>set","b be BinOp-of N","m be Element-of N"
  "cluster [#carrier\<mapsto>N ; multF\<mapsto> b;OneF\<mapsto>m#] \<rightarrow> non trivial-struct"
proof
  let ?X = "[#carrier\<mapsto>N ; multF\<mapsto> b;OneF\<mapsto>m#]"
  have "the carrier of ?X = N" using the_selector_of_1[of ?X carrier N] aggr by ty_auto
  thus "?X is non trivial-struct" using struct_0_def_9 by ty_auto
qed

abbreviation algstr_0_def_26 ("Trivial-multLoopStr") where
(* "Trivial-multLoopStr \<equiv> [#carrier\<mapsto>{{}} ; multF\<mapsto> op2;OneF\<mapsto>op0#]" *)
   "Trivial-multLoopStr \<equiv> [# Trivial-multMagma; OneF \<mapsto> {} #]"

mtheorem algstr_0_cl_44:
  "cluster Trivial-multLoopStr \<rightarrow> 1-element-struct\<bar> strict (multLoopStr)"
proof(standard,auto)
  let ?T ="Trivial-multLoopStr"
  have T0[ty]: "?T be multLoopStr" by ty_auto
  hence T1: "the carrier of ?T={{}}"
    using aggr the_selector_of_1 by ty_auto
  thus T2: "Trivial-multLoopStr is 1-element-struct" using T0 struct_0_def_19_a by ty_auto
qed ty_auto

mtheorem algstr_0_cl_45:
  "cluster strict (multLoopStr)\<bar>1-element-struct for multLoopStr"
proof(standard,standard)
  show "Trivial-multLoopStr is strict (multLoopStr)\<bar>1-element-struct \<bar> multLoopStr" by mauto
qed

mtheorem algstr_0_cl_46:
  "cluster Trivial-multLoopStr \<rightarrow> mult-cancelable"
proof(standard,standard,auto)
  let ?T ="Trivial-multLoopStr"
  have T1: "the carrier of ?T={{}}"
    using aggr the_selector_of_1 by ty_auto
  show "?T is right-mult-cancelable"
  proof(standard,auto)
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is right-mult-cancelable\<^sub>?T"
      proof(standard,auto)
        fix y z assume T3[ty]: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "y \<otimes>\<^sub>?T x = z \<otimes>\<^sub>?T x"
        show "y = z" using struct_0_def_10E[THEN bspec,THEN bspec,of ?T y z] by mauto
      qed ty_auto
    qed mauto
  show "?T is left-mult-cancelable"
    proof(standard,auto)
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is left-mult-cancelable\<^sub>?T"
      proof(standard,auto)
        fix y z assume T3[ty]: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "x \<otimes>\<^sub>?T y = x \<otimes>\<^sub>?T z"
        show "y = z" using struct_0_def_10E[THEN bspec,THEN bspec,of ?T y z] by mauto
      qed ty_auto
    qed mauto
qed ty_auto


mdef algstr_0_def_27 ("left-invertible\<^sub>_" [200] 200)where
   mlet "M be multLoopStr""attr left-invertible\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       (ex y be Element-of-struct M st y \<otimes>\<^sub>M x =1\<^sub>M))".

mdef algstr_0_def_28 ("right-invertible\<^sub>_" [200] 200)where
  mlet "M be multLoopStr""attr right-invertible\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       (ex y be Element-of-struct M st x \<otimes>\<^sub>M y =1\<^sub>M))".

mdef algstr_0_def_29 ("mult-invertible\<^sub>_" [200] 200)where
  mlet "M be multLoopStr"" attr mult-invertible\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       x is right-invertible\<^sub>M \<bar> left-invertible\<^sub>M)".

mtheorem algstr_0_cl_47:
  mlet "M be multLoopStr"
  "cluster right-invertible\<^sub>M \<bar> left-invertible\<^sub>M \<rightarrow> mult-invertible\<^sub>M for Element-of-struct M"
proof
   show "\<forall>it : Element-of-struct M. it is right-invertible\<^sub>M \<bar> left-invertible\<^sub>M \<longrightarrow> it is mult-invertible\<^sub>M"
     using algstr_0_def_29 by ty_auto
 qed mauto
   
mtheorem algstr_0_cl_48:
  mlet "M be multLoopStr"
   "cluster mult-invertible\<^sub>M \<rightarrow> right-invertible\<^sub>M \<bar> left-invertible\<^sub>M for Element-of-struct M"
using algstr_0_def_29 by ty_auto

text_raw {*\DefineSnippet{algstr0def30}{*}

mdef algstr_0_def_30 ("'/\<^sub>_ _" [1000, 99] 98) where
  mlet "M be multLoopStr",
          "x be Element-of-struct M"
  "assume x is left-invertible\<^sub>M \<bar> right-mult-cancelable\<^sub>M
   func /\<^sub>M x \<rightarrow> Element-of-struct M means
     (\<lambda>it. it \<otimes>\<^sub>M x = 1\<^sub>M)"
text_raw {*}%EndSnippet*}
proof-
     assume[ty]: "x is left-invertible\<^sub>M \<bar>right-mult-cancelable\<^sub>M"
     show "ex y be Element-of-struct M st y \<otimes>\<^sub>M x= 1\<^sub>M" using algstr_0_def_27[THEN iffD1] by mauto
  next
     assume A1[ty]: "x is (left-invertible\<^sub>M \<bar>right-mult-cancelable\<^sub>M)"
     fix y1 y2
        have I:"inhabited(Element-of-struct M)" by auto
     assume T0[ty]: "y1 be Element-of-struct M"
                "y2 be Element-of-struct M"
     assume
    A2: " y1 \<otimes>\<^sub>M x= 1\<^sub>M" and
    A3: " y2 \<otimes>\<^sub>M x= 1\<^sub>M"
    thus "y1=y2" using algstr_0_def_21E[of M x,THEN bspec,THEN bspec] by mauto (* Example for the need of mby *)
qed simp_all

mdef algstr_0_def_31 ("left-invertible")where
   "attr left-invertible for multLoopStr means (\<lambda> M.  (for x be Element-of-struct M holds x is left-invertible\<^sub>M))".


mdef algstr_0_def_32 ("right-invertible")where
   "attr right-invertible for multLoopStr means (\<lambda> M.
                                       (for x be Element-of-struct M holds x is right-invertible\<^sub>M))".

mdef algstr_0_def_33 ("invertible")where
   "attr invertible for multLoopStr means (\<lambda> M.
                                       M is right-invertible \<bar> left-invertible)".

mtheorem algstr_0_cl_49:
  "cluster right-invertible \<bar> left-invertible \<rightarrow> invertible for multLoopStr" 
using algstr_0_def_33 by auto

mtheorem algstr_0_cl_50:
  "cluster invertible \<rightarrow> right-invertible \<bar> left-invertible for multLoopStr"
using algstr_0_def_33 by auto

mtheorem algstr_0_cl_51:
  "cluster Trivial-multLoopStr \<rightarrow> invertible"
proof(standard,standard,auto)
  let ?T ="Trivial-multLoopStr"
  have [ty]:"?T be multLoopStr" by mauto
  have T1: "the carrier of ?T={{}}"
    using aggr the_selector_of_1 by ty_auto
  have Z: "1\<^sub>?T be Element-of-struct ?T" by mauto
  show "?T is right-invertible"
    proof(standard,auto)
      fix x assume T2[ty]:"x be Element-of-struct ?T"
      hence T3: "(x \<otimes>\<^sub>?T x) be Element-of-struct ?T" by infer_auto
      show "x is right-invertible\<^sub>?T"
      proof
        show "x be Element-of-struct ?T" by ty_simp
        have "x \<otimes>\<^sub>?T x =1\<^sub>?T" using struct_0_def_10E[THEN bspec,THEN bspec,of ?T "x \<otimes>\<^sub>?T x" "1\<^sub>?T"] by mauto
        thus "ex y be Element-of-struct ?T st x \<otimes>\<^sub>?T y =1\<^sub>?T" using bexI[of _ x] by mauto
      qed ty_auto
    qed mauto
  show "?T is left-invertible"
    proof(standard,auto)
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is left-invertible\<^sub>?T"
      proof
        show "x be Element-of-struct ?T" by ty_simp
        have "x \<otimes>\<^sub>?T x =1\<^sub>?T" using struct_0_def_10E[THEN bspec,THEN bspec,of ?T "x \<otimes>\<^sub>?T x" "1\<^sub>?T"] by mauto
        thus "ex y be Element-of-struct ?T st y \<otimes>\<^sub>?T x =1\<^sub>?T" using bexI[of _ x] by mauto
      qed ty_auto
    qed mauto
qed mauto

mtheorem algstr_0_cl_52:
  "cluster invertible\<bar>mult-cancelable\<bar>strict (multLoopStr)\<bar>1-element-struct for multLoopStr"
proof(standard,standard)
     show "Trivial-multLoopStr is invertible\<bar>mult-cancelable\<bar>strict (multLoopStr)\<bar>1-element-struct\<bar> multLoopStr"
        by infer_auto
qed

mtheorem algstr_0_cl_53:
  mlet "M be left-invertible \<bar> multLoopStr"
   "cluster \<rightarrow> left-invertible\<^sub>M for Element-of-struct M"
proof(standard,standard)
  fix X assume T[ty]: "X be Element-of-struct M"
  show "X be left-invertible\<^sub>M" using algstr_0_def_31E by mauto
qed mauto
  
mtheorem algstr_0_cl_54:
  mlet "M be right-invertible \<bar> multLoopStr"
   "cluster \<rightarrow> right-invertible\<^sub>M for Element-of-struct M"
proof(standard,standard)
  fix X assume T[ty]: "X be Element-of-struct M"
  show "X be right-invertible\<^sub>M" using algstr_0_def_32E by mauto
qed mauto

(*begin :: Almost*)
abbreviation "multLoopStr_0_fields \<equiv> (#carrier \<rightarrow> set';  multF\<rightarrow> BinOp-of' the' carrier; ZeroF \<rightarrow> Element-of' the' carrier;
      OneF \<rightarrow> Element-of' the' carrier #)"

mdef multLoopStr_0 ("multLoopStr'_0") where
  "struct [multLoopStr \<bar>ZeroOneStr]
        multLoopStr_0 (#carrier \<rightarrow> set';  multF\<rightarrow> BinOp-of' the' carrier; ZeroF \<rightarrow> Element-of' the' carrier;
      OneF \<rightarrow> Element-of' the' carrier #) defined on {carrier} \<union>{multF}\<union>{ZeroF}\<union>{OneF}"
  by (auto simp add: multLoopStr ZeroOneStr,
     auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

mtheorem
   mlet "X be set","B be BinOp-of X"," Z be Element-of X"," E be Element-of X"
   "cluster [#carrier\<mapsto>X ; multF\<mapsto>B ; ZeroF\<mapsto>Z ; OneF\<mapsto>E#] \<rightarrow> strict(multLoopStr_0)"
unfolding multLoopStr_0_def
    by (auto,rule struct_aggr_ancesors_rule, 
        auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string) ty_auto

mtheorem algstr_0_cl_55:
  mlet "D be non empty\<bar>set","o be BinOp-of D","d be Element-of D","e be Element-of D"
   "cluster [#carrier\<mapsto>D ; multF\<mapsto>o ; ZeroF\<mapsto>d ; OneF\<mapsto>e#] \<rightarrow> non empty-struct"
proof
  let ?X = "[#carrier\<mapsto>D ; multF\<mapsto>o ; ZeroF\<mapsto>d ; OneF\<mapsto>e#]"
  have T1[ty]: "?X be multLoopStr_0" by mauto
  have "the carrier of ?X = D" using the_selector_of_1[of ?X carrier D] aggr by ty_auto
  thus "?X is non empty-struct" using struct_0_def_1 by ty_auto
qed

mtheorem algstr_0_cl_56:
  mlet "T be trivial\<bar>set" , "f be BinOp-of T", "s be Element-of T"," t be Element-of T"
   "cluster [#carrier\<mapsto>T ; multF\<mapsto>f ; ZeroF\<mapsto>s ; OneF\<mapsto>t#] \<rightarrow> trivial-struct"
proof
  let ?X = "[#carrier\<mapsto>T ; multF\<mapsto>f ; ZeroF\<mapsto>s ; OneF\<mapsto>t#]"
  have T2: "the carrier of ?X = T" using the_selector_of_1[of ?X carrier T] aggr by ty_auto
  thus "?X is trivial-struct" using struct_0_def_9 by ty_auto
qed

mtheorem algstr_0_cl_57:
  mlet "N be non trivial\<bar>set","b be BinOp-of N","m be Element-of N","n be Element-of N"
   "cluster [#carrier\<mapsto>N ; multF\<mapsto>b ; ZeroF\<mapsto>m ; OneF\<mapsto>n#] \<rightarrow> non trivial-struct"
proof
  let ?X = "[#carrier\<mapsto>N ; multF\<mapsto>b ; ZeroF\<mapsto>m ; OneF\<mapsto>n#]"
  have T2: "the carrier of ?X = N" using the_selector_of_1[of ?X carrier N] aggr by ty_auto
  show "?X is non trivial-struct" using struct_0_def_9 T2 by ty_auto
qed

abbreviation algstr_0_def_34 ("Trivial-multLoopStr'_0") where
  "Trivial-multLoopStr_0 \<equiv>
     [# Trivial-multMagma; ZeroF \<mapsto> {} ; OneF \<mapsto> {} #]"

mtheorem algstr_0_cl_58:
  "cluster Trivial-multLoopStr_0 \<rightarrow> 1-element-struct\<bar> strict (multLoopStr_0)"
proof(standard,auto)
  let ?T ="Trivial-multLoopStr_0"
  have T0[ty]: "?T be multLoopStr_0" by mauto
  hence T1: "the carrier of ?T={{}}"
    using aggr the_selector_of_1 by ty_auto
  thus T2: "Trivial-multLoopStr_0 is 1-element-struct" using struct_0_def_19_a by ty_auto
qed ty_auto

mtheorem algstr_0_cl_59:
  "cluster strict (multLoopStr_0)\<bar>1-element-struct for multLoopStr_0"
proof(standard,standard)
  show "Trivial-multLoopStr_0 is strict (multLoopStr_0)\<bar>1-element-struct\<bar>multLoopStr_0" by infer_auto
qed

mdef algstr_0_def_36 ("almost-left-cancelable") where
   "attr almost-left-cancelable for multLoopStr_0 means (\<lambda> M.
                                       (for x be Element-of-struct M st x \<noteq> 0\<^sub>M holds x is left-mult-cancelable\<^sub>M))".

mdef algstr_0_def_37 ("almost-right-cancelable")where
   "attr almost-right-cancelable for multLoopStr_0 means (\<lambda> M.
                                       (for x be Element-of-struct M st x \<noteq> 0\<^sub>M holds x is right-mult-cancelable\<^sub>M))".

mdef algstr_0_def_38 ("almost-cancelable")where
   "attr almost-cancelable for multLoopStr_0 means (\<lambda> M.  M is almost-right-cancelable \<bar> almost-left-cancelable)".

mtheorem algstr_0_cl_60:
  "cluster almost-right-cancelable \<bar> almost-left-cancelable \<rightarrow> almost-cancelable for multLoopStr_0" 
using algstr_0_def_38 by auto

mtheorem algstr_0_cl_61:
  "cluster almost-cancelable \<rightarrow> almost-right-cancelable \<bar> almost-left-cancelable for multLoopStr_0" 
using algstr_0_def_38 by mauto
  
mtheorem algstr_0_cl_62:
  "cluster Trivial-multLoopStr_0 \<rightarrow> almost-cancelable"
proof(standard,standard,auto)
  let ?T ="Trivial-multLoopStr_0"
       show "?T is almost-right-cancelable"
        proof(standard,auto)
          fix x assume T2[ty]: "x be Element-of-struct ?T"
          assume "x \<noteq>0\<^sub>?T"
          thus "x is right-mult-cancelable\<^sub>?T" using struct_0_def_10E[THEN bspec,THEN bspec,of ?T x] by mauto
        qed mauto
       show "?T is almost-left-cancelable"
        proof(standard,auto)
          fix x assume T2[ty]: "x be Element-of-struct ?T"
          assume "x \<noteq>0\<^sub>?T"
          thus "x is left-mult-cancelable\<^sub>?T"
            using struct_0_def_10E[THEN bspec,THEN bspec,of ?T x] by mauto
        qed mauto
   qed ty_auto

mtheorem algstr_0_cl_63:
  "cluster almost-cancelable\<bar>strict (multLoopStr_0)\<bar>1-element-struct for multLoopStr_0"
proof(standard,standard)
  show "Trivial-multLoopStr_0 is almost-cancelable\<bar>strict (multLoopStr_0)\<bar>1-element-struct\<bar>multLoopStr_0"
  by infer_auto
qed

mdef algstr_0_def_39 ("almost-left-invertible")where
   "attr almost-left-invertible for multLoopStr_0 means (\<lambda> M.
                                       (for x be Element-of-struct M st x \<noteq> 0\<^sub>M holds x is left-invertible\<^sub>M))".

mdef algstr_0_def_40 ("almost-right-invertible")where
   "attr almost-right-invertible for multLoopStr_0 means (\<lambda> M.
                                       (for x be Element-of-struct M st x \<noteq> 0\<^sub>M holds x is right-invertible\<^sub>M))".

mdef algstr_0_def_41 ("almost-invertible")where
   "attr almost-invertible for multLoopStr_0 means (\<lambda> M.  M is almost-right-invertible \<bar> almost-left-invertible)".

mtheorem algstr_0_cl_64:
  "cluster almost-right-invertible \<bar> almost-left-invertible \<rightarrow> almost-invertible for multLoopStr_0" 
using algstr_0_def_41 by auto

mtheorem algstr_0_cl_65:
  "cluster almost-invertible \<rightarrow> almost-right-invertible \<bar> almost-left-invertible for multLoopStr_0" 
using algstr_0_def_41 by auto
  
mtheorem algstr_0_cl_66:
  "cluster Trivial-multLoopStr_0 \<rightarrow> almost-invertible"
proof(standard,standard,auto)
  let ?T ="Trivial-multLoopStr_0"
       have Z: "0\<^sub>?T be Element-of-struct ?T" using struct_0_def_6[of ?T] by mauto
       show "?T is almost-right-invertible"
        proof(standard,auto)
          fix x assume T2[ty]: "x be Element-of-struct ?T"
          assume "x \<noteq>0\<^sub>?T"
          thus "x is right-invertible\<^sub>?T" using struct_0_def_10E[THEN bspec,THEN bspec,of ?T x] by mauto
        qed mauto
       show "?T is almost-left-invertible"
        proof(standard,auto)
          fix x assume T2[ty]: "x be Element-of-struct ?T"
          assume "x \<noteq>0\<^sub>?T"
          thus "x is left-invertible\<^sub>?T" using struct_0_def_10E[THEN bspec,THEN bspec,of ?T x] by mauto
        qed mauto
   qed ty_auto

mtheorem algstr_0_cl_67:
  "cluster almost-invertible\<bar>almost-cancelable\<bar>strict (multLoopStr_0)\<bar>1-element-struct for multLoopStr_0"
 unfolding inhabited_def
proof(standard,standard)
  show "Trivial-multLoopStr_0 is almost-invertible\<bar>almost-cancelable\<bar>strict (multLoopStr_0)\<bar>1-element-struct\<bar>multLoopStr_0"
    by mauto
qed

(*begin :: Double*)

text_raw {*\DefineSnippet{doubleLoopStr_ex}{*}
term "{[carrier, the set]} \<union>
      {[addF, the BinOp-of (the set)]} \<union>
      {[ZeroF, the Element-of (the set)]} \<union>
      {[multF, the BinOp-of (the set)]} \<union>
      {[OneF, the Element-of (the set)]}"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{doubleLoopStr}{*}
mdef doubleLoopStr("doubleLoopStr") where
"struct [multLoopStr_0\<bar> addLoopStr]doubleLoopStr (#
   carrier \<rightarrow> (\<lambda>S. set);
   addF \<rightarrow> (\<lambda>S. BinOp-of the carrier of S);
   ZeroF \<rightarrow> (\<lambda>S. Element-of the carrier of S);
   multF \<rightarrow> (\<lambda>S. BinOp-of the carrier of S);
   OneF \<rightarrow> (\<lambda>S. Element-of the carrier of S)
#) defined on {carrier}\<union>{addF}\<union>{ZeroF}\<union>{multF}\<union>{OneF}"
  by (auto simp add: multLoopStr_0 addLoopStr,
     auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)
print_theorems
text_raw {*}%EndSnippet*}
print_theorems

mtheorem strict_doubleLoopStr:
  mlet "X be set",   "A be BinOp-of X","Z be Element-of X",
   "M be BinOp-of X","E be Element-of X"
   "cluster [#carrier\<mapsto>X; addF\<mapsto>A; ZeroF\<mapsto>Z; multF\<mapsto>M; OneF\<mapsto>E#] \<rightarrow> strict(doubleLoopStr)"
unfolding doubleLoopStr_def
    by (auto,rule struct_aggr_ancesors_rule, 
        auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string) ty_auto

text_raw {*\DefineSnippet{doubleLoopStr_strict}{*}
term "strict (doubleLoopStr) \<bar> doubleLoopStr"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{doubleLoopStr_dom}{*}
theorem "domain_of doubleLoopStr =
     {carrier} \<union> {addF} \<union> {ZeroF} \<union> {multF} \<union> {OneF}"
text_raw {*}%EndSnippet*}
using doubleLoopStr_dom by simp


text_raw {*\DefineSnippet{doubleLoopStr_agg_e}{*}
theorem
  "[#carrier\<mapsto>X;addF\<mapsto>A;ZeroF\<mapsto>Z;multF\<mapsto>M;OneF\<mapsto>E#] =
    {[carrier,X]}\<union>{[addF,A]}\<union>{[ZeroF,Z]}\<union>{[multF,M]}\<union>{[OneF,E]}" using aggr_def sel_t_def by simp
text_raw {*}%EndSnippet*}

  
  
 
mdef doubleLoopStrFixCarrier ("_-carrier doubleLoopStr") where
  mlet "C be non empty\<bar>set"
  "func C -carrier doubleLoopStr  \<rightarrow> set means
     (\<lambda>it. for x be object holds x in it iff x be strict(doubleLoopStr)& the carrier of x = C  )"  
proof-
  have [ty]: "Funcs([:C,C:],C) is set" using all_set by auto
  let ?F = "[: [: Funcs([:C,C:],C) , C:] , [: Funcs([:C,C:],C),C :]  :]"
  let ?CC = "\<lambda> x. [#carrier\<mapsto>C; addF\<mapsto>(x `1 `1);ZeroF\<mapsto>((x`1) `2);multF\<mapsto>((x `2) `1);OneF\<mapsto>((x`2) `2)#]"
  let ?P="\<lambda> x y. y = ?CC(x)"
  have P: "\<forall>x,y,z:object. ?P(x,y) \<and> ?P(x,z) \<longrightarrow> y = z" by auto
  
  obtain X where [ty]: "X be set" and
   X: "\<forall>x:object.
   x in X \<longleftrightarrow> (\<exists>y:object. y in ?F \<and> ?P(y,x))" using tarski_0_sch_1[of ?F ?P,OF _ P] by infer_auto

  show "ex x be set st for xa be object holds (xa in x \<longleftrightarrow> xa be strict(doubleLoopStr) & the carrier of xa = C)"
  proof(rule bexI[of _ X],standard,rule iffI3)
    fix  x  
    show "x in X \<longrightarrow> x be strict(doubleLoopStr) \<and> the carrier of x = C"
    proof
      assume "x in X"
      then obtain y where
        A1: "y in ?F & ?P(y,x)" using X by auto
      then obtain y1 y2 y3 y4 where
        B2: "y1 in Funcs([:C,C:],C) & y2 in C & y3 in Funcs([:C,C:],C) & y4 in C & y = [[y1,y2],[y3,y4]]" 
         using zfmisc_th_4[of C "Funcs([:C,C:],C)" C "Funcs([:C,C:],C)" y,simplified] all_set by ty_auto
      obtain f where A2[ty]: "f be Function" and
         A3: " y1 = f \<and> dom f = [:C,C:] \<and> rng f c= C" using funct_2_def_2 B2 by ty_auto
      obtain g where A4[ty]: "g be Function" and
         A5: " y3 = g \<and> dom g = [:C,C:] \<and> rng g c= C" using funct_2_def_2 B2 by ty_auto
   
      have [ty]: "f is BinOp-of C" "g is BinOp-of C" using funct_2_th_3[of C f] funct_2_th_3[of C g] A3 A5 by ty_auto
      have [ty]:"y2 is Element-of C" "y4 is Element-of C" using Element(6) B2 by ty_auto

      have "y `1 = [f,y2]" using B2 A3 xtuple_0_reduce by auto
      hence H1: "f = y `1 `1" "y2 = y `1 `2" using xtuple_0_reduce by auto 
      have "y `2 = [g,y4]" using B2 A5 xtuple_0_reduce by auto
      hence H2: "g = y `2 `1" "y4 = y `2 `2" using xtuple_0_reduce by auto 

      have A4: "[#carrier\<mapsto>C; addF\<mapsto>f; ZeroF\<mapsto>y2; multF\<mapsto>g; OneF\<mapsto>y4#] is strict(doubleLoopStr)" by infer_auto
      have "the carrier of [#carrier\<mapsto>C; addF\<mapsto>f; ZeroF\<mapsto>y2; multF\<mapsto>g; OneF\<mapsto>y4#] = C"  using 
        the_selector_of_1[of _ "carrier"] aggr Struct_2 string by infer_auto
      then show "x be strict(doubleLoopStr) \<and> the carrier of x = C" using A1 A3 A4 H1 H2 by auto           
    qed
    have [ty]: "[:C,C:] is set" using all_set by auto
    assume A5: "x be strict(doubleLoopStr) \<and> the carrier of x = C"
    hence [ty]: "x be strict(doubleLoopStr)" by simp
    let ?A = "the addF of x" let ?M="the multF of x"
    have [ty]: "?A is BinOp-of C" "?M is BinOp-of C" using A5 by infer_auto
    have [ty]: "?A be Function" "?M be Function" by ty_auto
    have "dom ?A = [:C,C:]" "rng ?A c= C" "dom ?M = [:C,C:]" "rng ?M c= C" using binop_1_mode_2[of C] A5 relat_1_def_19E[of C] by ty_auto
    hence B: "?A in Funcs([:C,C:],C)" "?M in Funcs([:C,C:],C)" using funct_2_def_2[of "[:C,C:]" C] by ty_auto
    let ?Z = "the ZeroF of x" let ?O="the OneF of x"  
    have [ty]: "?Z is Element-of C" "?O is Element-of C" using A5 by infer_auto
    hence E: "?Z in C" "?O in C" using Element(7) by ty_auto
    obtain XX where 
    XX: "XX = [[?A,?Z],[?M,?O]]" by simp
    have "[?A,?Z] in [: Funcs([:C,C:],C) , C:]" "[?M,?O] in [: Funcs([:C,C:],C) , C:]" using B E zfmisc_1_th_87 by ty_auto
    hence Q1: "XX in ?F" using zfmisc_1_th_87 XX by infer_auto
    have "?CC(XX) = x"
    proof(rule Equal_strict[of _ _ doubleLoopStr],ty_auto)
      have "XX `1 = [?A,?Z]" "XX `2 = [?M,?O]" using xtuple_0_reduce XX by auto
      hence H1: "?A = XX `1 `1" "?Z = XX `1 `2"  "?M = XX `2 `1" "?O = XX `2 `2" using xtuple_0_reduce by auto 
      hence [ty]: "XX `1 `1 is  BinOp-of C" "XX `2 `1 is  BinOp-of C" 
          "XX `1 `2 is  Element-of C" "XX `2 `2 is  Element-of C" using H1 by infer_auto
      hence [ty]: "?CC(XX) is strict(doubleLoopStr)" using strict_doubleLoopStr[of C "XX `1 `1" "XX `1 `2" "XX `2 `1" "XX `2 `2",simplified]
        by ty_auto
      then show [ty]: "?CC(XX) is Struct" "?CC(XX) is strict(doubleLoopStr)" by infer_auto
      fix sel assume B1: "sel in domain_of doubleLoopStr"
      hence S: "sel = carrier or sel = addF or sel = ZeroF or sel = multF or
           sel = OneF " using string doubleLoopStr_dom by auto
     have T:"the carrier of ?CC(XX)=C" "the addF of ?CC(XX)=?A"  "the ZeroF of ?CC(XX)=?Z"
       "the multF of ?CC(XX)=?M"  "the OneF of ?CC(XX)=?O"
        using the_selector_of_1[of _ "carrier"]  the_selector_of_1[of _ "addF"] 
        the_selector_of_1[of _ "ZeroF"]
              the_selector_of_1[of _ "multF"] the_selector_of_1[of _ "OneF"] aggr H1 by ty_auto
     then show "the sel of ?CC(XX) = the sel of x" using S A5 by auto 
   qed
    then show "x in X" using Q1 X by auto
  qed mauto
  fix IT1 IT2 assume [ty]: "IT1 be set" "IT2 be set" 

  assume A1: "for x being object holds (x in IT1 \<longleftrightarrow> x be strict(doubleLoopStr) \<and> the' carrier(x) = C)"
     and A2: "for x being object holds (x in IT2 \<longleftrightarrow> x be strict(doubleLoopStr) \<and> the' carrier(x) = C)"
  {
      fix x
      assume T1:"x be object"
      have "x in IT1 \<longleftrightarrow> x be strict(doubleLoopStr) \<and> the' carrier(x) = C" using A1 T1 by auto
      then have "x in IT1 \<longleftrightarrow> x in IT2" using A2 T1 by auto
  }
  thus "IT1 = IT2" by (intro tarski_th_2) ty_auto
qed mauto
  
  


mtheorem algstr_0_cl_68:
  mlet "D be non empty\<bar>set","o be BinOp-of D","o1 be BinOp-of D","d be Element-of D","e be Element-of D"
   "cluster [#carrier\<mapsto>D;addF\<mapsto>o;ZeroF\<mapsto>d;multF\<mapsto>o1;OneF\<mapsto>e#] \<rightarrow> non empty-struct"
proof
  let ?X = " [#carrier\<mapsto>D;addF\<mapsto>o;ZeroF\<mapsto>d;multF\<mapsto>o1;OneF\<mapsto>e#]"
  have T1[ty]: "?X be doubleLoopStr" by mauto
  have "the carrier of ?X = D" using the_selector_of_1[of ?X carrier D] aggr by ty_auto
  thus "?X is non empty-struct" using struct_0_def_1 by ty_auto
qed

mtheorem algstr_0_cl_69:
  mlet "T be trivial\<bar>set","f be BinOp-of T","f1 be BinOp-of T","s be Element-of T","t be Element-of T"
   "cluster [#carrier\<mapsto>T;addF\<mapsto>f;ZeroF\<mapsto>t;multF\<mapsto>f1;OneF\<mapsto>s#] \<rightarrow> trivial-struct"
proof
  let ?X = "[#carrier\<mapsto>T;addF\<mapsto>f;ZeroF\<mapsto>t;multF\<mapsto>f1;OneF\<mapsto>s#]"
  have [ty]: "?X be doubleLoopStr" by mauto
  hence "the carrier of ?X = T" using aggr the_selector_of_1 by ty_auto
  thus "?X is trivial-struct" using struct_0_def_9 by mauto
qed

mtheorem algstr_0_cl_70:
  mlet "N be non trivial\<bar>set","b be BinOp-of N","b1 be BinOp-of N","n be Element-of N","m be Element-of N"
   "cluster [#carrier\<mapsto>N;addF\<mapsto>b;ZeroF\<mapsto>m;multF\<mapsto>b1;OneF\<mapsto>n#] \<rightarrow> non trivial-struct"
proof
  let ?X = "[#carrier\<mapsto>N;addF\<mapsto>b;ZeroF\<mapsto>m;multF\<mapsto>b1;OneF\<mapsto>n#]"
  have [ty]: "?X be doubleLoopStr" by mauto
  hence "the carrier of ?X = N" using aggr the_selector_of_1 by ty_auto
  thus "?X is non trivial-struct" using struct_0_def_9 by ty_auto
qed

abbreviation algstr_0_def_42 ("Trivial-doubleLoopStr") where
(*  "Trivial-doubleLoopStr \<equiv>
     [#carrier\<mapsto>{{}};addF\<mapsto>op2;ZeroF\<mapsto>op0;multF\<mapsto>op2;OneF\<mapsto>op0#]"*)
  "Trivial-doubleLoopStr \<equiv>
     [# Trivial-addLoopStr; multF \<mapsto> op2 ; OneF \<mapsto> {} #]"

mtheorem algstr_0_cl_71:
  "cluster Trivial-doubleLoopStr \<rightarrow> 1-element-struct\<bar> strict (doubleLoopStr)"
proof(standard,auto)
  let ?T ="Trivial-doubleLoopStr"
  have T0[ty]: "?T be doubleLoopStr" by mauto
  hence T1: "the carrier of ?T={{}}"
    using aggr the_selector_of_1 by ty_auto
  thus T2: "Trivial-doubleLoopStr is 1-element-struct" using T0 struct_0_def_19_a by ty_auto
qed ty_auto

mtheorem algstr_0_cl_72:
  "cluster strict (doubleLoopStr)\<bar>non empty-struct\<bar>1-element-struct for doubleLoopStr"
proof(standard,standard)
  show "Trivial-doubleLoopStr is strict (doubleLoopStr)\<bar>non empty-struct\<bar>1-element-struct\<bar>doubleLoopStr" by infer_auto
qed

mtheorem algstr_0_cl_72_add:
  "cluster non empty-struct for doubleLoopStr"
proof(standard,standard)
  show "Trivial-doubleLoopStr is non empty-struct\<bar>doubleLoopStr" by infer_auto
qed

mdef algstr_0_def_43 ("_ '/\<^sub>_ _" [66,1000, 67] 66) where
  mlet "M be multLoopStr","x be Element-of-struct M","y be Element-of-struct M"
  "func x /\<^sub>M y \<rightarrow> Element-of-struct M equals
     x \<otimes>\<^sub>M /\<^sub>M y"
proof-
    show "(x \<otimes>\<^sub>M /\<^sub>M y) be Element-of-struct M" by ty_auto
qed

text_raw {*\DefineSnippet{addLoopStrEx1}{*}
term "{[carrier, the set]} \<union>
      {[addF, the BinOp-of (the set)]} \<union>
      {[ZeroF, the Element-of (the set)]}"
text_raw {*}%EndSnippet*}




text_raw {*\DefineSnippet{addLoopStrEx2}{*}
term "[#carrier \<mapsto> (the set);
      addF\<mapsto> the BinOp-of (the set);
      ZeroF\<mapsto> the Element-of (the set)#]"
text_raw {*}%EndSnippet*}

  
  
end
