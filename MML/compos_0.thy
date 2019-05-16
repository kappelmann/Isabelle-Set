theory compos_0
  imports finseq_1

begin



mdef compos_0_def_1 ("standard-ins") where
  "attr standard-ins for set means (\<lambda>S. ex X be non empty\<bar>set st S c= [:NAT, NAT*,X*:])"..

mdef compos_0_synonym_1 ("InsCode _" [130] 130) where
mlet "x be object"
     "synonym func InsCode x for x`1`1"..
    
mdef compos_0_synonym_2 ("JumpPart _" [130] 130) where 
  mlet "x be object" 
  "synonym func JumpPart x for x`1`2"..
mdef compos_0_synonym_3 ("AddressPart _" [130] 130) where 
  mlet "x be object" 
  "synonym func AddressPart x for x`2"..

text_raw {*\DefineSnippet{instruction}{*}
term "[InsCode i, JumpPart i, AddressPart i]"
text_raw {*}%EndSnippet*}

mtheorem compos_0_cl_1:
  mlet "S be non empty \<bar>standard-ins\<bar>set",
       "I be Element-of S"
   "cluster AddressPart I \<rightarrow> FinSequence-like \<bar> Function_like \<bar> Relation_like"
proof
  obtain X where
     [ty]:"X be non empty \<bar>set" and A2: "S c= [:NAT, NAT*,X*:]" using compos_0_def_1 by mauto
  have "I in S" using Element_of[of S I] by auto
  hence "I in [:NAT, NAT*,X*:]" using tarski_def_3 A2 by mauto
  then obtain i1 i2 i3 where
     "i1 be object" "i2 be object"  "i3 be object" and
    A3: "I = [[i1,i2],i3] \<and> i1 in NAT \<and> i2 in NAT* \<and> i3 in X*" using zfmisc_3[of "X*" "NAT*" "NAT" I] by mauto
  have "AddressPart I = i3" using compos_0_synonym_3 A3 xtuple_0_reduce by auto
  hence [ty]:"AddressPart I be FinSequence-of X" using A3 finseq_1_def_11 A2 by auto
  thus "AddressPart I is FinSequence-like \<bar> Function_like \<bar> Relation_like" by mauto
qed

mtheorem compos_0_cl_2:
  mlet "S be non empty \<bar>standard-ins \<bar>set","
       I be Element-of S"
   "cluster JumpPart I \<rightarrow> FinSequence-like \<bar> Function_like \<bar> Relation_like"
proof
  obtain X where
    [ty]: "X be non empty \<bar>set" and A2: "S c= [:NAT, NAT*,X*:]" using compos_0_def_1 by mauto
  have "I in S" using Element_of[of S I] by auto
  hence "I in [:NAT, NAT*,X*:]" using A2 tarski_def_3 by mauto
  then obtain i1 i2 i3 where
     "i1 be object" "i2 be object"  "i3 be object" and
    A3: "I = [[i1,i2],i3] \<and> i1 in NAT \<and> i2 in NAT* \<and> i3 in X*" using zfmisc_3[of "X*" "NAT*" "NAT" I] by mauto
  have "JumpPart I = i2" using compos_0_synonym_2 A3 xtuple_0_reduce by auto
  hence [ty]:"JumpPart I be FinSequence-of NAT" using A3 finseq_1_def_11 all_set by auto
  thus "JumpPart I is FinSequence-like \<bar> Function_like \<bar> Relation_like" by auto
qed

mdef compos_0_def_2 ("InsCodes _") where
  mlet "S be set"
  "func InsCodes S \<rightarrow> set equals
     proj1 (proj1 S)" by mauto


abbreviation compos_0_mode_1 ("InsType-of _") where
  "InsType-of S \<equiv> Element-of InsCodes S"

mtheorem compos_0_redef_1:
  mlet "S be non empty \<bar>standard-ins \<bar>set",
       "I be Element-of S"
  "redefine func InsCode I \<rightarrow> InsType-of S"
proof
  obtain X where
    [ty]: "X be non empty \<bar>set" and A2: "S c= [:NAT, NAT*,X*:]" using compos_0_def_1 by mauto
  have B1: "I in S" using Element_of[of S I] by auto

  hence "I in [:NAT, NAT*,X*:]" using tarski_def_3 A2 by mauto
  then obtain i1 i2 i3 where
     "i1 be object" "i2 be object"  "i3 be object" and
    A3: "I = [[i1,i2],i3] \<and> i1 in NAT \<and> i2 in NAT* \<and> i3 in X*" using zfmisc_3[of "X*" "NAT*" "NAT" I] by mauto
  have A4: "InsCode I = i1" using compos_0_synonym_1 A3 xtuple_0_reduce by auto
  have "[i1,i2] in proj1 S" using xtuple_0_def_12 all_set B1 A3 by auto
  hence "i1 in InsCodes S" using xtuple_0_def_12 all_set B1 A3 compos_0_def_2 by auto
  hence "i1 be Element-of InsCodes S" using Element_of_rule3 by mauto
  thus "InsCode I be InsType-of S" using A4 by auto
qed

text_raw {*\DefineSnippet{compos_0_def_3}{*}
mdef compos_0_def_3 ("JumpParts _ , _") where
  mlet "S be non empty \<bar>standard-ins \<bar>set",
           "T be InsType-of S"
  "func JumpParts I , T \<rightarrow> set equals
     {JumpPart i where i be Element-of I: InsCode i = T }"
text_raw {*}%EndSnippet*}
  by mauto

mdef compos_0_def_4 ("AddressParts _ , _") where
  mlet "S be non empty\<bar>standard-ins\<bar>set",
           "T be InsType-of S"
  "func AddressParts S , T \<rightarrow> set equals
     { AddressPart I where I be Element-of S: InsCode I = T }"
by mauto

text_raw {*\DefineSnippet{compos_0_def_5}{*}
mdef compos_0_def_5 ("homogeneous")where
  "attr homogeneous for non empty\<bar>standard-ins\<bar>set means (\<lambda>I.
      for i,j be Element-of I st InsCode i = InsCode j holds
         dom JumpPart i = dom JumpPart j)"..
text_raw {*}%EndSnippet*}

  text_raw {*\DefineSnippet{compos_0_def_7}{*}
mdef compos_0_def_7 ("J|A-independent")where
  "attr J|A-independent for non empty\<bar>standard-ins\<bar>set means (\<lambda>I.
     for n be Nat, f1,f2 be NAT-valued \<bar>Function, p be object
        st dom f1 = dom f2 \<and> [n,f1,p] in I holds [n,f2,p] in I)"..
  text_raw {*}%EndSnippet*}


text_raw {*\DefineSnippet{compos_0_def_10}{*}
mdef compos_0_def_10 ("with'_halt")where
  "attr with_halt for set means (\<lambda>S. [{},{},{}] in S)"..
text_raw {*}%EndSnippet*}

mdef compos_0_def_11 ("halt _" [100] 100) where
  mlet "S be with_halt \<bar>set"
  "func halt S \<rightarrow> Element-of S equals
     [{},{},{}]"
proof-
  have "[{},{},{}] in S" using compos_0_def_10 by mauto
  thus "[{},{},{}] be Element-of S" using Element_of_rule3 by mauto
qed

mtheorem compos_0_cl_10:
  "cluster with_halt \<rightarrow> non empty for set"
proof(standard,auto)
  fix X assume A1[ty]: "X be set" "X is with_halt"
  hence "[{},{},{}] in X" using compos_0_def_10 by mauto
  thus "X is empty\<Longrightarrow>False" using xboole_0_def_1 all_set by auto
qed

text_raw {*\DefineSnippet{Instructions}{*}
abbreviation
  "Instructions \<equiv> J|A-independent\<bar>homogeneous\<bar>with_halt\<bar>standard-ins\<bar>set"
text_raw {*}%EndSnippet*}
theorem Instructions_non_empty:
  "X be Instructions \<Longrightarrow> X is non empty"
proof-
  assume "X be Instructions"
  hence "[{},{},{}] in X" using compos_0_def_10 by auto
  thus "X is non empty" using xboole_0_def_1 all_set by auto
qed

theorem Instructions_ex:
  "{[{},{},{}]} be Instructions"
proof-
  let ?x = "[{},{},{}]"
  let ?I = "{?x}"
  have W1[ty]: "?I is standard-ins"
  proof
    show "ex X be non empty \<bar>  set st ?I \<subseteq> [: NAT , NAT* , X* :]"
    proof(rule bexI[of _ NAT],rule tarski_def_3I,auto)
      fix x assume "x in {?x}"
      hence A1:"x=?x" using tarski_def_1 by auto
      have A2: "{} in NAT" "{} in NAT*" using ordinal1_def_11 finseq_1_th by mauto
      hence "[{},{}] in [:NAT,NAT*:]" using zfmisc_1_def_2 by mauto
      hence "x in [: [:NAT , NAT*:] , NAT* :]" using A1 A2 zfmisc_1_def_2 by mauto
      thus "x in [: NAT , NAT* , NAT* :]" using zfmisc_1_def_3 by mty auto
    qed mauto
  qed mauto
  have W2[ty]:"?I is with_halt" using tarski_def_1 compos_0_def_10 by mauto
  have W3[ty]:"?I is non empty" by mauto
  have W4[ty]: "?I is homogeneous"
  proof(standard,auto)
    fix I J
    assume [ty]:"I be Element-of ?I" "J be Element-of ?I"
    hence "I in ?I" "J in ?I" using W3 Element_of by mauto
    hence "I=?x" "J=?x" using tarski_def_1 by auto
    thus "dom JumpPart I = dom JumpPart J" by simp
  qed mauto
  have [ty]:"?I is J|A-independent"
  proof(standard,auto)
    fix T f1 f2 p
    assume [ty]:  "T be natural" "T be set" "f1 be NAT -valued"
      "f1 is Function_like"
       "f1 is Relation_like"
       "f1 is set"
       "f2 be NAT -valued"
       "f2 is Function_like"
       "f2 is Relation_like"
       "f2 is set" and A1:
 "dom f1 = dom f2 " " [T , f1 , p] in ?I"
    have "[T , f1 , p] in ?I" using A1 by auto
    hence L: "[T , f1 , p] = ?x" using tarski_def_1 by auto
    have L1:"[T,f1] = [{},{}]" using xtuple_0_th_1[rule_format, OF L] by auto
    have F: "f1 = {}" using xtuple_0_th_1[rule_format, OF L1] by auto
    have "dom {} is empty" by mty auto
    hence "dom {} = {}" using xboole_0_lm_1 by mauto
    hence "f1=f2" using relat_1_th_41 A1 F by mauto
    thus "[T , f2 , p] in ?I" using A1 by auto
  qed mauto
  thus ?thesis by mauto
qed

mtheorem
  "cluster J|A-independent\<bar>homogeneous\<bar>with_halt\<bar>standard-ins for set"
proof(standard,standard)
  show "{[{},{},{}]} be Instructions" using Instructions_ex by simp
qed


end

