theory vectsp_1
imports z2 rlvect_1 group_1
begin

mtheorem Z2_cl_7:
  "cluster Z \<rightarrow> add-associative \<bar> right-zeroed \<bar> right-complementable \<bar> Abelian \<bar> non empty-struct"
proof(standard,auto)
(*  have [ty]: "Z be doubleLoopStr" by auto *)
  show "Z is add-associative"
  proof(standard,auto)

    fix u v w assume T1[ty]: "u be Element-of-struct Z" "v be Element-of-struct Z"  "w be Element-of-struct Z"
    have A1: "u=ONE \<or> u = ZERO" "v=ONE \<or> v = ZERO" "w=ONE \<or> w = ZERO" using Z2d(3) by simp_all
    show "u \<oplus>\<^sub>Z v \<oplus>\<^sub>Z w = u \<oplus>\<^sub>Z (v \<oplus>\<^sub>Z w)" using Z2d(6,7,8,9) A1 by auto
  qed
  show "Z is right-zeroed"
  proof(standard,auto)
     fix v assume [ty]:"v be Element-of-struct Z"
     hence "v=ONE \<or> v = ZERO" using Z2d(3) by simp
     thus "v \<oplus>\<^sub>Z 0\<^sub>Z = v" using Z2d(3)[of v] Z2d(4,6,8) by mty auto
   qed
  show "Z is right-complementable"
  proof(standard,auto,standard)
    fix x assume A1[ty]:"x be Element-of-struct Z"
    show "\<exists>y be Element-of-struct Z. x \<oplus>\<^sub>Z y = 0\<^sub>Z"
      proof(rule bexI[of _ x])
        have "x=ONE \<or> x = ZERO" using A1 Z2d(3) by simp
        thus "x \<oplus>\<^sub>Z x = 0\<^sub>Z" using A1 Z2d(4,6,9)  by auto
      qed auto
  qed auto
  show "Z is Abelian"
  proof(standard,auto)
    fix u v assume T1[ty]: "u be Element-of-struct Z" "v be Element-of-struct Z"
    hence A1: "u=ONE \<or> u = ZERO" "v=ONE \<or> v = ZERO" using Z2d(3) by simp+
    show "u \<oplus>\<^sub>Z v = v \<oplus>\<^sub>Z u" using Z2d(6,7,8,9) A1 by auto
   qed
  have [ty]: "the carrier of Z is non empty" using Z2d(14) by mty auto
  thus "Z is empty-struct\<Longrightarrow> False" using struct_0_def_1 by auto
qed

mtheorem vectsp_1_cl_7:
  "cluster add-associative\<bar>right-zeroed\<bar>right-complementable\<bar> Abelian for
    non empty-struct\<bar>addLoopStr"
proof(standard,standard)
  show "Z is add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>Abelian\<bar>(non empty-struct\<bar>addLoopStr)" by mty auto
qed

abbreviation(input)
  "AddGroup \<equiv> add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>(non empty-struct\<bar>addLoopStr)"

abbreviation (input)
  "AbGroup \<equiv> Abelian\<bar>AddGroup"

mdef vectsp_1_def_2 ("right-distributive")where
   "attr right-distributive for non empty-struct\<bar>doubleLoopStr means (\<lambda> M.
     (for a,b,c be Element-of-struct M holds a \<otimes>\<^sub>M (b \<oplus>\<^sub>M c) = a \<otimes>\<^sub>M b \<oplus>\<^sub>M a \<otimes>\<^sub>M c))"..

lemma "inhabited(non empty-struct\<bar>doubleLoopStr)" by auto

mdef vectsp_1_def_3 ("left-distributive")where
   "attr left-distributive for non empty-struct\<bar>doubleLoopStr means (\<lambda> M.
     (for a,b,c be Element-of-struct M holds (b \<oplus>\<^sub>M c) \<otimes>\<^sub>M a = b \<otimes>\<^sub>M a \<oplus>\<^sub>M c \<otimes>\<^sub>M a))"..

mdef vectsp_1_def_4 ("right-unital")where
   "attr right-unital for non empty-struct\<bar>multLoopStr means (\<lambda> M.
     (for a be Element-of-struct M holds a \<otimes>\<^sub>M 1\<^sub>M = a))"..

mdef vectsp_1_def_6 ("well-unital")where
   "attr well-unital for non empty-struct\<bar>multLoopStr means (\<lambda> M.
     (for a be Element-of-struct M holds a \<otimes>\<^sub>M 1\<^sub>M = a \<and> 1\<^sub>M \<otimes>\<^sub>M a = a))"..

mtheorem Z2_cl_15:
  "cluster Z \<rightarrow> well-unital"
proof(standard,standard,auto)
  fix a assume A1[ty]: "a be Element-of-struct Z"
  have "a \<otimes>\<^sub>Z 1\<^sub>Z = a \<and> (1\<^sub>Z) \<otimes>\<^sub>Z a = a"
    proof (cases "a=ONE")
      case True
       thus ?thesis using Z2d(5,11,13) Z2d(3)[of a] by auto next
      case False
        thus ?thesis using Z2d(5,11,12) Z2d(3)[of a] A1 by auto next
      qed
   thus "a \<otimes>\<^sub>Z 1\<^sub>Z = a " " (1\<^sub>Z) \<otimes>\<^sub>Z a = a" by auto
  qed mauto

mtheorem 
  "cluster non empty-struct for multLoopStr_0"
proof(standard,standard)
  show "Z is non empty-struct\<bar>multLoopStr_0" by mty auto
qed

mtheorem vectsp_1_cl_15:
  "cluster well-unital for non empty-struct\<bar>multLoopStr_0"
proof(standard,standard)
  show "Z is well-unital\<bar>(non empty-struct\<bar>multLoopStr_0)" by mty auto
qed

mtheorem vectsp_1_reduce_1:
  mlet "L be well-unital \<bar> (non empty-struct\<bar>multLoopStr_0)",
       "x be Element-of-struct L"
  "reduce x\<otimes>\<^sub>L 1\<^sub>L to x"
proof
  show "x \<otimes>\<^sub>L 1\<^sub>L = x" using vectsp_1_def_6E[of L ] by mauto
qed
  
mtheorem vectsp_1_reduce_2:
  mlet "L be well-unital\<bar>non empty-struct\<bar>multLoopStr_0",
       "x be Element-of-struct L"
  "reduce (1\<^sub>L) \<otimes>\<^sub>L x to x"
proof
  show "1\<^sub>L \<otimes>\<^sub>L x = x" using vectsp_1_def_6E[of L ] by mty auto
qed
  
mdef vectsp_1_def_7 ("distributive")where
   "attr distributive for non empty-struct\<bar>doubleLoopStr means (\<lambda> M.
     (for a,b,c be Element-of-struct M holds a \<otimes>\<^sub>M (b \<oplus>\<^sub>M c) = a \<otimes>\<^sub>M b \<oplus>\<^sub>M a \<otimes>\<^sub>M c \<and> (b \<oplus>\<^sub>M c) \<otimes>\<^sub>M a = b \<otimes>\<^sub>M a \<oplus>\<^sub>M c \<otimes>\<^sub>M a))"..


mdef vectsp_1_def_8 ("left-unital")where
   "attr left-unital for non empty-struct\<bar>doubleLoopStr means (\<lambda> M.
     (for a be Element-of-struct M holds 1\<^sub>M \<otimes>\<^sub>M a = a))"..


mtheorem vectsp_1_def_9:
  "redefine attr almost-left-invertible for non empty-struct\<bar>multLoopStr_0 
means
     \<lambda>M. for x be Element-of-struct M st x \<noteq> 0\<^sub>M holds ex y be Element-of-struct M st y \<otimes>\<^sub>M x = 1\<^sub>M"
proof(standard,rule ballI, rule iffI3 )
  fix M assume [ty]:"M be non empty-struct\<bar>multLoopStr_0"
  show "M is almost-left-invertible \<longrightarrow> (for x be Element-of-struct M st x \<noteq>0\<^sub>M holds ex y be Element-of-struct M st y \<otimes>\<^sub>M x = 1\<^sub>M)"
    using algstr_0_def_39E[of M] algstr_0_def_27E[of M] by auto
  assume A1: "for x be Element-of-struct M st x \<noteq>0\<^sub>M holds ex y be Element-of-struct M st y \<otimes>\<^sub>M x = 1\<^sub>M"
  show "M is almost-left-invertible"
  proof(standard,auto,standard)
    fix x assume [ty]:"x be Element-of-struct M" and "x \<noteq>0\<^sub>M"
    thus "ex y be Element-of-struct M st y \<otimes>\<^sub>M x = 1\<^sub>M" using A1 by auto
  qed auto
qed mauto

mtheorem vectsp_1_cl_20:
  "cluster distributive \<rightarrow> left-distributive \<bar>right-distributive for
    non empty-struct \<bar>doubleLoopStr"
proof(standard,auto)
  fix M assume [ty]:"\<not> M be empty-struct "" M be doubleLoopStr" "M be distributive"
  show "M be left-distributive"
  proof(standard,auto)
    fix a b c assume [ty]:"a be Element-of-struct M" "b be Element-of-struct M" "c be Element-of-struct M"
    show "(b \<oplus>\<^sub>M c) \<otimes>\<^sub>M a = b \<otimes>\<^sub>M a \<oplus>\<^sub>M c \<otimes>\<^sub>M a" using vectsp_1_def_7E[THEN bspec,THEN bspec,THEN bspec,of M a b c]  by auto
  qed
  show "M be right-distributive"
  proof(standard,auto)
    fix a b c assume [ty]:"a be Element-of-struct M" "b be Element-of-struct M" "c be Element-of-struct M"
    show "a \<otimes>\<^sub>M (b \<oplus>\<^sub>M c) = a \<otimes>\<^sub>M b \<oplus>\<^sub>M a \<otimes>\<^sub>M c" using vectsp_1_def_7E[THEN bspec,THEN bspec,THEN bspec,of M a b c]  by auto
  qed
qed

mtheorem vectsp_1_cl_21:
  "cluster left-distributive \<bar>right-distributive \<rightarrow> distributive for
    non empty-struct \<bar>doubleLoopStr"
proof(standard,standard,standard,standard,simp,intro ballI)
  fix M assume [ty]: "M be non empty-struct\<bar> doubleLoopStr" "M be left-distributive \<bar>right-distributive"
   fix a b c assume [ty]:"a be Element-of-struct M" "b be Element-of-struct M" "c be Element-of-struct M"
   show "a \<otimes>\<^sub>M (b \<oplus>\<^sub>M c) = a \<otimes>\<^sub>M b \<oplus>\<^sub>M a \<otimes>\<^sub>M c \<and> (b \<oplus>\<^sub>M c) \<otimes>\<^sub>M a = b \<otimes>\<^sub>M a \<oplus>\<^sub>M c \<otimes>\<^sub>M a" 
     using vectsp_1_def_3E[THEN bspec,THEN bspec,THEN bspec,of M a b c]
      vectsp_1_def_2E[THEN bspec,THEN bspec,THEN bspec,of M a b c] by mty auto
 qed auto

mtheorem vectsp_1_cl_22:
  "cluster well-unital \<rightarrow> left-unital \<bar>right-unital for
    non empty-struct \<bar>doubleLoopStr"
proof(standard,auto)
  fix M assume [ty]:"\<not>M be empty-struct" "M be doubleLoopStr" "M be well-unital"
  show "M be left-unital"
  proof(standard,auto)
    fix a assume [ty]:"a be Element-of-struct M"
    show "1\<^sub>M \<otimes>\<^sub>M a = a" using vectsp_1_def_6E[of M ]  by auto
  qed
  show "M be right-unital"
  proof(standard,auto)
    fix a assume [ty]:"a be Element-of-struct M"
    show " a \<otimes>\<^sub>M 1\<^sub>M = a" using vectsp_1_def_6E[of M ]  by auto
  qed
qed

mtheorem vectsp_1_cl_23:
  "cluster left-unital \<bar>right-unital \<rightarrow> well-unital for
    non empty-struct \<bar>doubleLoopStr"
proof(standard,standard,standard,standard)
  fix M assume [ty]:"M be non empty-struct\<bar> doubleLoopStr" "M be left-unital \<bar>right-unital"
  show "M is non empty-struct \<bar>multLoopStr" by mauto
  show "\<forall>a : Element-of-struct M. a \<otimes>\<^sub>M 1\<^sub>M = a \<and> 1\<^sub>M \<otimes>\<^sub>M a = a"
    proof
  fix a assume [ty]:"a be Element-of-struct M"
  show "a \<otimes>\<^sub>M 1\<^sub>M = a \<and> 1\<^sub>M \<otimes>\<^sub>M a = a" using vectsp_1_def_4E[of M ]  vectsp_1_def_8E[of M ]  by auto
   qed mauto
  qed mauto

mtheorem Z2_cl_24:
  "cluster Z \<rightarrow> commutative\<bar>associative\<bar>unital"
proof(standard,auto)
  have A1[ty]: "Z be doubleLoopStr" by mty auto
  show "Z is commutative"
  proof(standard,auto)
    fix u v assume T1[ty]: "u be Element-of-struct Z" "v be Element-of-struct Z"
    hence A1: "u=ONE \<or> u = ZERO" "v=ONE \<or> v = ZERO" using Z2d(3) by simp+
    show "u \<otimes>\<^sub>Z v = v \<otimes>\<^sub>Z u" using Z2d(11,12) A1 by auto
  qed
  show "Z is associative"
      proof(standard,auto)
        fix u v w assume T1[ty]: "u be Element-of-struct Z" "v be Element-of-struct Z"  "w be Element-of-struct Z"
         hence "u=ONE \<or> u = ZERO" "v=ONE \<or> v = ZERO" "w=ONE \<or> w = ZERO" using Z2d(3) by simp+
         thus "u \<otimes>\<^sub>Z v \<otimes>\<^sub>Z w = u \<otimes>\<^sub>Z (v \<otimes>\<^sub>Z w)" using Z2d(10,11,12,13) by auto
      qed mauto
  show "Z is unital"
  proof(intro group_1_def_1I bexI[of _ "1\<^sub>Z"] ballI)
    show "1\<^sub>Z be Element-of-struct Z" by (simp add:Z2d(2,5))
    fix h assume A1:"h be Element-of-struct Z"
    hence "h=ONE \<or> h=ZERO" "1\<^sub>Z = ONE" using Z2d(5,3) by auto
    thus "h \<otimes>\<^sub>Z 1\<^sub>Z = h \<and> 1\<^sub>Z \<otimes>\<^sub>Z h = h" using Z2d(11,12,13) by auto
  qed auto
qed

mtheorem vectsp_1_cl_24:
  "cluster commutative\<bar>associative for non empty-struct \<bar>multMagma"
proof(standard,standard)
   show "Z is commutative\<bar>associative\<bar>(non empty-struct \<bar>multMagma)" by mty auto
 qed


mtheorem vectsp_1_cl_25:
  "cluster commutative\<bar>associative\<bar>unital for non empty-struct \<bar>multLoopStr"
proof(standard,standard)
   show "Z is commutative\<bar>associative\<bar>unital\<bar>(non empty-struct \<bar>multLoopStr)" by mty auto
 qed

mtheorem Z2_cl_26:
  "cluster Z \<rightarrow> almost-left-invertible\<bar>distributive\<bar>non degenerated\<bar>strict (doubleLoopStr)"
proof(standard,simp,intro conjI)
  have A1[ty]: "Z be doubleLoopStr" by mty auto
  show "Z is almost-left-invertible"
  proof(standard,auto,standard,simp,simp,rule bexI[of _ "1\<^sub>Z"]) (* bexI[of _ _ "1\<^sub>Z"]*)
    fix x assume [ty]:"x be Element-of-struct Z" and "x \<noteq> 0\<^sub>Z"
    thus "1\<^sub>Z \<otimes>\<^sub>Z x = 1\<^sub>Z" "1\<^sub>Z be Element-of-struct Z" using Z2d(3)[of x] Z2d(2,4,5,13) by auto
  qed auto
  show "\<not>Z is degenerated" using struct_0_def_8nI Z2d(4,5) by auto
  show "Z is distributive"
  proof(standard,mauto)
      fix u v w assume [ty]: "u be Element-of-struct Z" "v be Element-of-struct Z"  "w be Element-of-struct Z"
      have A1: "u=ONE \<or> u = ZERO" "v=ONE \<or> v = ZERO" "w=ONE \<or> w = ZERO" using Z2d(3) by mty auto
    have "u \<otimes>\<^sub>Z (v \<oplus>\<^sub>Z w) = (u \<otimes>\<^sub>Z v) \<oplus>\<^sub>Z (u \<otimes>\<^sub>Z w) \<and> (v \<oplus>\<^sub>Z w) \<otimes>\<^sub>Z u = (v \<otimes>\<^sub>Z u) \<oplus>\<^sub>Z (w \<otimes>\<^sub>Z u)"
    proof (cases "u=ONE")
      case True
        thus ?thesis using Z2d(6,7,8,9,10,11,12,13) A1 by auto
     next
        case False
          thus ?thesis using Z2d(6,7,8,9,10,11,12,13) A1 by auto
        qed
     thus "u \<otimes>\<^sub>Z (v \<oplus>\<^sub>Z w) = (u \<otimes>\<^sub>Z v) \<oplus>\<^sub>Z (u \<otimes>\<^sub>Z w) "" (v \<oplus>\<^sub>Z w) \<otimes>\<^sub>Z u = (v \<otimes>\<^sub>Z u) \<oplus>\<^sub>Z (w \<otimes>\<^sub>Z u)" by auto
  qed
qed

mtheorem
"cluster associative \<bar> commutative \<bar> well-unital \<bar> distributive \<bar> almost-left-invertible for non empty-struct \<bar> doubleLoopStr"
proof(standard,standard)
  show "Z is associative \<bar> commutative \<bar> well-unital \<bar> distributive \<bar> almost-left-invertible \<bar> (non empty-struct \<bar> doubleLoopStr)"
   by mauto
qed 
mtheorem
  "cluster add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>
  right-distributive for non empty-struct \<bar>doubleLoopStr"
proof(standard,standard)
  show "Z is  add-associative \<bar> right-zeroed \<bar> right-complementable \<bar> right-distributive \<bar> (non empty-struct \<bar> doubleLoopStr)"
    by mauto
qed

mtheorem
  "cluster add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>
  left-distributive for non empty-struct \<bar>doubleLoopStr"
proof(standard,standard)
  show "Z is add-associative \<bar> right-zeroed \<bar> right-complementable \<bar> left-distributive \<bar> (non empty-struct \<bar> doubleLoopStr)"
    by mauto
 qed



mtheorem
  "cluster add-associative \<bar> right-zeroed \<bar> right-complementable \<bar> distributive for non empty-struct \<bar>doubleLoopStr"
proof(standard,standard)
  show "Z is add-associative \<bar> right-zeroed \<bar> right-complementable \<bar> distributive \<bar> (non empty-struct \<bar> doubleLoopStr)" by mauto
qed

mtheorem
  "cluster add-associative \<bar> right-zeroed \<bar>
         right-complementable \<bar> associative \<bar> commutative \<bar>
         well-unital \<bar> almost-left-invertible \<bar>
         distributive for non empty-struct \<bar> doubleLoopStr"
proof(standard,standard)
  show "Z is  add-associative \<bar> right-zeroed \<bar> right-complementable \<bar> associative \<bar> commutative \<bar> well-unital \<bar> almost-left-invertible \<bar>
    distributive \<bar>
    (non empty-struct \<bar> doubleLoopStr)"
   by mauto
qed


 text_raw {*\DefineSnippet{vectsp1cl26}{*}
mtheorem vectsp_1_cl_26:
 "cluster add-associative \<bar> right-zeroed \<bar> right-complementable \<bar>
          Abelian \<bar> commutative \<bar> associative \<bar> left-unital\<bar>
          right-unital \<bar> distributive \<bar> almost-left-invertible\<bar>
          non degenerated \<bar> well-unital \<bar> strict (doubleLoopStr)
     for non empty-struct \<bar> doubleLoopStr"
  text_raw {*}%EndSnippet*}
proof(standard,standard)
  show "Z is add-associative \<bar> right-zeroed \<bar> right-complementable \<bar> Abelian \<bar> commutative \<bar> associative \<bar> left-unital \<bar> right-unital \<bar>
    distributive \<bar>
    almost-left-invertible \<bar>
    non degenerated \<bar>
    well-unital \<bar>
    strict(doubleLoopStr) \<bar>
    (non empty-struct \<bar> doubleLoopStr)"
   by mauto
qed


text_raw {*\DefineSnippet{Ring}{*}
abbreviation
 "Ring \<equiv> Abelian \<bar> add-associative \<bar> right-zeroed \<bar>
          right-complementable \<bar> associative \<bar>
          well-unital \<bar> distributive \<bar>
          non empty-struct \<bar> doubleLoopStr"
text_raw {*}%EndSnippet*}


text_raw {*\DefineSnippet{RingFixCarrier}{*}
mdef RingFixCarrier ("_-carrier-ring") where
  mlet "C be non empty\<bar>set"
  "func C -carrier-ring  \<rightarrow> set means
     (\<lambda>it. for x be object holds x in it iff x be strict(doubleLoopStr) \<bar> Ring & the carrier of x = C ) "  
text_raw {*}%EndSnippet*}
proof-
  let ?P = "\<lambda> x . x be Ring" 
  let ?AM = "C -carrier doubleLoopStr"
  let ?Q = "\<lambda> y. y be strict(doubleLoopStr) \<bar> Ring \<and> the carrier of y = C"
  obtain X where
   [ty]: "X be set" and
   A1: "for x be object holds x in X iff x in ?AM & ?P(x)" using xboole_0_sch_1[of ?AM ?P] all_set by mty auto
  show "\<exists>X : set. \<forall>y : object. y in X \<longleftrightarrow> ?Q(y)" 
  proof(rule bexI[of _ X],rule ballI)
    fix y   
    show "y in X \<longleftrightarrow> ?Q(y)" using A1 doubleLoopStrFixCarrier by mty auto     
  qed mauto
    fix IT1 IT2 assume [ty]: "IT1 be set" "IT2 be set" 

  assume A1: "for x being object holds (x in IT1 \<longleftrightarrow> ?Q(x))"
     and A2: "for x being object holds (x in IT2 \<longleftrightarrow> ?Q(x))"
  {
      fix x
      assume T1:"x be object"
      have "x in IT1 \<longleftrightarrow> ?Q(x)" using A1 T1 by auto
      then have "x in IT1 \<longleftrightarrow> x in IT2" using A2 T1 by auto
  }
  thus "IT1 = IT2" by (intro tarski_th_2) auto
qed mauto



text_raw {*\DefineSnippet{SkewField}{*}
abbreviation
 "SkewField \<equiv> non degenerated \<bar>
                     almost-left-invertible \<bar> Ring"
text_raw {*}%EndSnippet*}

  
text_raw {*\DefineSnippet{FIELD}{*}
abbreviation
  "Field \<equiv> commutative \<bar> SkewField"
text_raw {*}%EndSnippet*}

theorem vectsp_1_Field_Test:
  "ex R be Field st True" using inhabited_def exI[of _ Z]  by mty auto

mtheorem
  "cluster commutative for SkewField"
proof(standard,standard)
  show "Z is Field" by mty auto
qed

mtheorem vectsp_1_th_5:
  "for F be associative\<bar>commutative\<bar>well-unital\<bar>distributive\<bar>
            almost-left-invertible \<bar>(non empty-struct\<bar>doubleLoopStr),
       x,y,z be Element-of-struct F
   st x \<noteq> 0\<^sub>F \<and> x \<otimes>\<^sub>F y = x \<otimes>\<^sub>F z holds y = z"
proof(intro ballI uncurry impI)
  fix F x y z assume T0[ty]: " F be associative \<bar> commutative \<bar> well-unital \<bar> distributive \<bar>
                         almost-left-invertible \<bar> (non empty-struct \<bar>doubleLoopStr)"
                 and T1[ty]: "x be Element-of-struct F"  "y be Element-of-struct F" "z be Element-of-struct F"
  have W1[ty]:  "F is left-unital" using vectsp_1_cl_22 by auto
  assume "x\<noteq>0\<^sub>F"
  then obtain x1 where T2[ty]:"x1 be Element-of-struct F" and
    A1: "x1 \<otimes>\<^sub>F x = 1\<^sub>F" using vectsp_1_def_9E[THEN bspec,of F x] by mty auto
  have A2: "(x1 \<otimes>\<^sub>F x) \<otimes>\<^sub>F y = x1 \<otimes>\<^sub>F (x \<otimes>\<^sub>F y) \<and> x1 \<otimes>\<^sub>F (x \<otimes>\<^sub>F z) = (x1 \<otimes>\<^sub>F x) \<otimes>\<^sub>F z" using group_1_def_3E[of F] by auto
  assume "x \<otimes>\<^sub>F y = x \<otimes>\<^sub>F z"
  hence "(x1 \<otimes>\<^sub>F x) \<otimes>\<^sub>F y = z" using A1 A2 vectsp_1_def_8E[THEN bspec] W1 by auto
  thus "y=z" using A1 A2 vectsp_1_def_8E[THEN bspec] W1 by auto
qed mauto

abbreviation inv (infix "\<hungarumlaut>\<^sup>" 105) where
  "x\<hungarumlaut>\<^sup>S \<equiv> /\<^sub>S x"


mtheorem vectsp_1_def_10:
  mlet "F be associative \<bar> commutative \<bar> well-unital \<bar>
       almost-left-invertible \<bar> (non empty-struct \<bar> doubleLoopStr)",
       "x be Element-of-struct F"
   "assume x \<noteq> 0\<^sub>F
   redefine func x\<hungarumlaut>\<^sup>F \<rightarrow> Element-of-struct F means
     (\<lambda>it. it \<otimes>\<^sub>F x = 1\<^sub>F)"
proof(standard)
  show [ty]: "x\<hungarumlaut>\<^sup>F be Element-of-struct F" by mty auto
 fix IT assume T0:"x \<noteq> 0\<^sub>F\<and>IT be Element-of-struct F"
 hence [ty]:"IT be Element-of-struct F" by auto

  have [ty]: "x is left-invertible\<^sub>F" using algstr_0_def_39E T0 by auto
  then obtain x1 where [ty]: "x1 be Element-of-struct F" and
    A3: "x1 \<otimes>\<^sub>F x = 1\<^sub>F" using algstr_0_def_27E[of F x] by auto
  have A3': "x \<otimes>\<^sub>F x1 = 1\<^sub>F"
    using group_1_def_12E[THEN bspec,THEN bspec,of F x1 x] A3 T0 by auto
  have [ty]: "x is right-mult-cancelable\<^sub>F"
   proof(standard,auto)
     fix y z assume [ty]: "y be Element-of-struct F"
                        "z be Element-of-struct F"
     assume A4: "y \<otimes>\<^sub>F x = z \<otimes>\<^sub>F x"
     have "y = y \<otimes>\<^sub>F 1\<^sub>F" using vectsp_1_def_6E[THEN bspec] by auto
     also have "\<dots> = z \<otimes>\<^sub>F x \<otimes>\<^sub>F x1"
       using A3' A4 group_1_def_3E[THEN bspec,THEN bspec,THEN bspec,of F y x x1]  by auto
     also have "\<dots> = z \<otimes>\<^sub>F 1\<^sub>F"
       using A3' A4 group_1_def_3E[THEN bspec,THEN bspec,THEN bspec,of F z x x1]  by auto
     also have "\<dots> = z " using vectsp_1_def_6E[THEN bspec] by auto
     finally show "y = z" by auto
   qed
   thus "IT = x\<hungarumlaut>\<^sup>F \<longleftrightarrow> IT \<otimes>\<^sub>F x = 1\<^sub>F"
     thm algstr_0_def_30 A
     using A algstr_0_def_30[of F x,simplified] algstr_0_def_30_uniq[of F x IT,simplified] by mty auto (* Jest wolne , ale dziala*)
qed

mtheorem vectsp_1_th_6:
  "for F be add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>
  right-distributive\<bar>(non empty-struct \<bar>doubleLoopStr), x be Element-of-struct F holds
   x \<otimes>\<^sub>F 0\<^sub>F = 0\<^sub>F"
proof (intro ballI)
  fix F x assume T0[ty]:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
    right-distributive\<bar>(non empty-struct \<bar>doubleLoopStr)" "x be Element-of-struct F"
  have "x \<otimes>\<^sub>F 0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F = x\<otimes>\<^sub>F(0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F) \<oplus>\<^sub>F 0\<^sub>F" using rlvect_1_th_4[of F] by mty auto
  also have "\<dots>= x\<otimes>\<^sub>F ( 0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F)" using rlvect_1_th_4[of F,THEN conjunct1] by mauto
  also have "\<dots>= x\<otimes>\<^sub>F 0\<^sub>F \<oplus>\<^sub>F x \<otimes>\<^sub>F 0\<^sub>F" using vectsp_1_def_2E by mauto
  finally show " x \<otimes>\<^sub>F 0\<^sub>F = 0\<^sub>F" using rlvect_1_th_8[of F "x \<otimes>\<^sub>F 0\<^sub>F"  "0\<^sub>F" "x \<otimes>\<^sub>F 0\<^sub>F"]  by mty auto
qed mauto

mtheorem vectsp_1_reduce_3:
  mlet "F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
            right-distributive\<bar>non empty-struct \<bar>doubleLoopStr",
       "x be Element-of-struct F",
       "y be Zero \<^sub>F \<bar> Element-of-struct F"
   "reduce x \<otimes>\<^sub>F y to y"
proof
  have "y=0\<^sub>F" using struct_0_def_12E by mauto
  thus "x \<otimes>\<^sub>F y = y" using vectsp_1_th_6[of F x] by auto
qed

mtheorem vectsp_1_th_7:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
     left-distributive\<bar>(non empty-struct \<bar>doubleLoopStr), x be Element-of-struct F holds
     0\<^sub>F \<otimes>\<^sub>F x = 0\<^sub>F"
proof (intro ballI)
  fix F x assume T0[ty]:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
    left-distributive\<bar>(non empty-struct \<bar>doubleLoopStr)" "x be Element-of-struct F"
  have "0\<^sub>F \<otimes>\<^sub>F x \<oplus>\<^sub>F 0\<^sub>F = ( 0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F)\<otimes>\<^sub>F x \<oplus>\<^sub>F 0\<^sub>F" using rlvect_1_th_4[of F "0\<^sub>F"] by mty auto
  also have "\<dots>= ( 0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F)\<otimes>\<^sub>F x" using rlvect_1_th_4[of F] by mauto
  also have "\<dots>=  0\<^sub>F \<otimes>\<^sub>F x \<oplus>\<^sub>F 0\<^sub>F \<otimes>\<^sub>F x" using vectsp_1_def_3E[of F] by mty auto
  finally show " 0\<^sub>F \<otimes>\<^sub>F x= 0\<^sub>F" using rlvect_1_th_8[of F "0\<^sub>F \<otimes>\<^sub>F x" "0\<^sub>F" "0\<^sub>F \<otimes>\<^sub>F x"]  by mty auto
qed mauto

mtheorem vectsp_1_reduce_4:
  mlet "F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
            left-distributive\<bar>non empty-struct \<bar>doubleLoopStr",
       "x be Element-of-struct F",
       "y be Zero \<^sub>F \<bar> Element-of-struct F"
   "reduce y \<otimes>\<^sub>F x to y"
proof
  have "y=0\<^sub>F" using struct_0_def_12E[of F] by mauto
  thus "y \<otimes>\<^sub>F x = y" using vectsp_1_th_7[of F x] by auto
qed

theorem vectsp_1_th_8[THEN bspec,THEN bspec,THEN bspec,rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
  right-distributive\<bar>(non empty-struct \<bar>doubleLoopStr), x,y be Element-of-struct F holds
   x \<otimes>\<^sub>F (\<ominus>\<^sub>F y) = \<ominus>\<^sub>F x \<otimes>\<^sub>F y"
proof (intro ballI)
  fix F x y assume T0[ty]:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
    right-distributive\<bar>(non empty-struct \<bar>doubleLoopStr)" "x be Element-of-struct F" "y be Element-of-struct F"

  have "(x \<otimes>\<^sub>F y) \<oplus>\<^sub>F (x \<otimes>\<^sub>F (\<ominus>\<^sub>F y)) = x \<otimes>\<^sub>F (y \<oplus>\<^sub>F \<ominus>\<^sub>F y)" using vectsp_1_def_2E[of F] by mty auto
  also have "\<dots>=x \<otimes>\<^sub>F 0\<^sub>F " using rlvect_1_def_10 by auto
  also have "\<dots>= 0\<^sub>F " using vectsp_1_th_6[of F] by auto
  finally show "x \<otimes>\<^sub>F (\<ominus>\<^sub>F y) = \<ominus>\<^sub>F x \<otimes>\<^sub>F y" using rlvect_1_def_10_uniq[of F "x \<otimes>\<^sub>F y" "x \<otimes>\<^sub>F (\<ominus>\<^sub>F y)"] by mty auto
qed auto

theorem vectsp_1_th_9[THEN bspec,THEN bspec,THEN bspec,rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
  left-distributive\<bar>(non empty-struct \<bar>doubleLoopStr), x,y be Element-of-struct F holds
  (\<ominus>\<^sub>F x) \<otimes>\<^sub>F y = \<ominus>\<^sub>F x \<otimes>\<^sub>F y"
proof (intro ballI)
  fix F x y assume T0[ty]:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
    left-distributive\<bar>(non empty-struct \<bar>doubleLoopStr)" "x be Element-of-struct F" "y be Element-of-struct F"
  have "(x \<otimes>\<^sub>F y) \<oplus>\<^sub>F ((\<ominus>\<^sub>F x) \<otimes>\<^sub>F y) =  (x \<oplus>\<^sub>F \<ominus>\<^sub>F x) \<otimes>\<^sub>F y" using vectsp_1_def_3E[of F]  by mty auto
  also have "\<dots>= 0\<^sub>F \<otimes>\<^sub>F y" using rlvect_1_def_10 by auto
  also have "\<dots>= 0\<^sub>F " using vectsp_1_th_7 T0 by auto
  finally show "(\<ominus>\<^sub>F x) \<otimes>\<^sub>F y = \<ominus>\<^sub>F x \<otimes>\<^sub>F y"
      using rlvect_1_def_10_uniq[of F "x \<otimes>\<^sub>F y" "(\<ominus>\<^sub>F x) \<otimes>\<^sub>F y"] by mty auto
qed auto

theorem vectsp_1_th_10[THEN bspec,THEN bspec,THEN bspec,rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
  distributive\<bar>(non empty-struct \<bar>doubleLoopStr), x,y be Element-of-struct F holds
  (\<ominus>\<^sub>F x) \<otimes>\<^sub>F (\<ominus>\<^sub>F y) =  x \<otimes>\<^sub>F y"
proof (intro ballI)
  fix F x y assume T0[ty]:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
    distributive\<bar>(non empty-struct \<bar>doubleLoopStr)" "x be Element-of-struct F" "y be Element-of-struct F"
  have "(\<ominus>\<^sub>F x) \<otimes>\<^sub>F (\<ominus>\<^sub>F y) = \<ominus>\<^sub>F x \<otimes>\<^sub>F (\<ominus>\<^sub>F y)" using vectsp_1_th_9[of F] by mty auto
  also have "\<dots> =   \<ominus>\<^sub>F \<ominus>\<^sub>F x \<otimes>\<^sub>F y" using vectsp_1_th_8[of F] vectsp_1_cl_20 by auto
  also have "\<dots> = x \<otimes>\<^sub>F y" using rlvect_1_th_17 by mty auto
  finally show "(\<ominus>\<^sub>F x) \<otimes>\<^sub>F (\<ominus>\<^sub>F y) =  x \<otimes>\<^sub>F y" by auto
qed auto

theorem vectsp_1_th_11[THEN bspec,THEN bspec,THEN bspec,THEN bspec,rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
            right-distributive\<bar>(non empty-struct \<bar>doubleLoopStr),
        x,y,z be Element-of-struct F holds
   x \<otimes>\<^sub>F (y \<ominus>\<^sub>F z) = x \<otimes>\<^sub>F y \<ominus>\<^sub>F x \<otimes>\<^sub>F z"
proof(intro ballI)
  fix F x y z
  assume T0[ty]:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar> right-distributive\<bar>(non empty-struct \<bar>doubleLoopStr)"
            "x be Element-of-struct F"
            "y be Element-of-struct F"
            "z be Element-of-struct F"
  have "x \<otimes>\<^sub>F (y \<ominus>\<^sub>F z) = x \<otimes>\<^sub>F y \<oplus>\<^sub>F x \<otimes>\<^sub>F (\<ominus>\<^sub>F z)" using vectsp_1_def_2E[THEN bspec,THEN bspec,THEN bspec] algstr_0_def_14 by mty auto
  also have "\<dots> = x \<otimes>\<^sub>F y \<ominus>\<^sub>F x \<otimes>\<^sub>F z" using vectsp_1_th_8 algstr_0_def_14 by mty auto
  finally show " x \<otimes>\<^sub>F (y \<ominus>\<^sub>F z) = x \<otimes>\<^sub>F y \<ominus>\<^sub>F x \<otimes>\<^sub>F z" by auto
qed auto

text_raw {*\DefineSnippet{vectsp1th12}{*}
theorem vectsp_1_th_12[THEN bspec,THEN bspec,THEN bspec,rule_format]:
  "for F being add-associative \<bar> right-zeroed \<bar>
         right-complementable \<bar> associative \<bar> commutative \<bar>
         well-unital \<bar> almost-left-invertible \<bar>
         distributive \<bar> (non empty-struct \<bar> doubleLoopStr),
       x,y being Element-of-struct F holds
    x \<otimes>\<^sub>F y = 0\<^sub>F \<longleftrightarrow> x = 0\<^sub>F \<or> y = 0\<^sub>F"
text_raw {*}%EndSnippet*}
proof(intro ballI)
  fix F x y
  assume T[ty]:"F be add-associative \<bar> right-zeroed \<bar>
          right-complementable \<bar> associative \<bar> commutative \<bar>
          well-unital \<bar> almost-left-invertible \<bar>
          distributive \<bar> (non empty-struct \<bar> doubleLoopStr)"
         "x be Element-of-struct F"
         "y be Element-of-struct F"
  have "x \<otimes>\<^sub>F y = 0\<^sub>F \<longrightarrow> x = 0\<^sub>F \<or> y = 0\<^sub>F"
    proof(rule impI,rule disjCI2)
      assume A1:"x \<otimes>\<^sub>F y = 0\<^sub>F"
      assume A2:"x \<noteq> 0\<^sub>F"
      have "x\<hungarumlaut>\<^sup>F \<otimes>\<^sub>F 0\<^sub>F = x\<hungarumlaut>\<^sup>F \<otimes>\<^sub>F x \<otimes>\<^sub>F y" using A1 group_1_def_3E by mty auto
      also have "\<dots> = 1\<^sub>F \<otimes>\<^sub>F y" using A2 vectsp_1_def_10 by auto
      also have "\<dots> = y" using vectsp_1_reduce_2 by auto
      finally show "y = 0\<^sub>F" using vectsp_1_reduce_3 by mty auto
    qed
  thus "x \<otimes>\<^sub>F y = 0\<^sub>F \<longleftrightarrow> x = 0\<^sub>F \<or> y = 0\<^sub>F" using
    vectsp_1_reduce_4 vectsp_1_reduce_3 by mauto
qed auto


text_raw {*\DefineSnippet{vectsp1th12_ex}{*}
reserve F for Field
reserve x,y for "Element-of-struct F"
mtheorem "x \<otimes>\<^sub>F y = 0\<^sub>F \<longleftrightarrow> x = 0\<^sub>F \<or> y = 0\<^sub>F"
text_raw {*}%EndSnippet*}
proof-
  have "x \<otimes>\<^sub>F y = 0\<^sub>F \<longrightarrow> x = 0\<^sub>F \<or> y = 0\<^sub>F"
    proof(rule impI,rule disjCI2)
      assume A1:"x \<otimes>\<^sub>F y = 0\<^sub>F"
      assume A2:"x \<noteq> 0\<^sub>F"
      have "x\<hungarumlaut>\<^sup>F \<otimes>\<^sub>F 0\<^sub>F = x\<hungarumlaut>\<^sup>F \<otimes>\<^sub>F x \<otimes>\<^sub>F y"
            using A1 group_1_def_3E by mty auto
        also have "\<dots> = 1\<^sub>F \<otimes>\<^sub>F y" using A2 vectsp_1_def_10 by auto
        also have "\<dots> = y" using vectsp_1_reduce_2 by auto
       finally show "y = 0\<^sub>F" using vectsp_1_reduce_3 by mty auto
    qed
  thus "x \<otimes>\<^sub>F y = 0\<^sub>F \<longleftrightarrow> x = 0\<^sub>F \<or> y = 0\<^sub>F" using
    vectsp_1_reduce_4 vectsp_1_reduce_3 by mauto
qed


theorem vectsp_1_th_13[rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
  left-distributive\<bar>(non empty-struct \<bar>doubleLoopStr), x,y,z be Element-of-struct F holds
   (y \<ominus>\<^sub>F z) \<otimes>\<^sub>F x = y \<otimes>\<^sub>F x \<ominus>\<^sub>F z \<otimes>\<^sub>F x"
proof(intro ballI)
  fix F x y z
  assume T0[ty]:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar> left-distributive\<bar>(non empty-struct \<bar>doubleLoopStr)"
            "x be Element-of-struct F"
            "y be Element-of-struct F"
            "z be Element-of-struct F"
  have "(y \<ominus>\<^sub>F z) \<otimes>\<^sub>F x = y \<otimes>\<^sub>F x \<oplus>\<^sub>F (\<ominus>\<^sub>F z) \<otimes>\<^sub>F x" using vectsp_1_def_3E[THEN bspec] algstr_0_def_14 by mty auto
  also have "\<dots> = y \<otimes>\<^sub>F x \<ominus>\<^sub>F z \<otimes>\<^sub>F x" using vectsp_1_th_9 algstr_0_def_14 by mty auto
  finally show "(y \<ominus>\<^sub>F z) \<otimes>\<^sub>F x = y \<otimes>\<^sub>F x \<ominus>\<^sub>F z \<otimes>\<^sub>F x" by auto
qed auto

abbreviation ModuleStr_fields_prefix ("ModuleStr'_fields _" [110] 110) where
 "ModuleStr_fields F \<equiv>(#carrier \<rightarrow> set';  addF\<rightarrow> BinOp-of' the' carrier; ZeroF \<rightarrow> Element-of' the' carrier;
               lmult \<rightarrow>  Function-of' [: the carrier of F,the' carrier ':], the' carrier #)"


mdef ModuleStr_over ("ModuleStr-over _") where
  mlet "F be 1-sorted"
  "struct [addLoopStr]
      ModuleStr-over F (#carrier \<rightarrow> set';  addF\<rightarrow> BinOp-of' the' carrier; ZeroF \<rightarrow> Element-of' the' carrier;
               lmult \<rightarrow>  Function-of' [: the carrier of F,the' carrier ':], the' carrier #)
       defined on {carrier}\<union>{addF}\<union>{ZeroF}\<union>{lmult}"
    by (auto simp add: addLoopStr,
     auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

   
thm ex   
   
mtheorem
  mlet "F be 1-sorted", "X be set",   "A be BinOp-of X", "z be Element-of X",
   "L be Function-of [: the carrier of F,X:],X" 
   "cluster [#carrier\<mapsto>X; addF\<mapsto>A; ZeroF\<mapsto>z; lmult\<mapsto>L #] \<rightarrow> strict(ModuleStr-over F)"
proof
  show " [#carrier\<mapsto>X; addF\<mapsto>A; ZeroF\<mapsto>z; lmult\<mapsto>L #] is strict(ModuleStr-over F)"
    unfolding  ModuleStr_over_def
    by (rule struct_aggr_ancesors_rule, 
        auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)
qed 
end
