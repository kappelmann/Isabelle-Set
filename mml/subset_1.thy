theory subset_1
imports zfmisc_1
begin

mtheorem subset_1_cl_1:
  mlet "X be set"
  "cluster bool X \<rightarrow> non empty"
   using xboole_0_def_1 zfmisc_1_def_1 tarski_def_3c by inst_nopass_auto
   
theorem empty1:
  "x is empty \<Longrightarrow> x={}"
proof(rule xboole_0_def_10I)
  assume A1: "x is empty"
  show "x \<subseteq> {}" "{} \<subseteq> x"
  proof -
    show "x \<subseteq> {}" using A1 all_set tarski_def_3 xboole_0_def_1 by auto
    have "{} is empty" by infer_auto
    thus "{} \<subseteq> x" using all_set tarski_def_3 xboole_0_def_1 by auto
  qed
qed (simp add: all_set)+

theorem empty2:
  "x is non empty \<Longrightarrow> x\<noteq>{} " using empty1 by infer_auto

(*term "mode2 Eleme(X) \<rightarrow> set means
   (\<lambda>it. (it in X if X is non empty otherwise it is empty))"
*)
mdef subset_1_def_1      ("Element-of _" [105] 105) where
  mlet "X be set"
  "mode Element-of X \<rightarrow> set means
   ((\<lambda>it. it in X) if (X is non empty) otherwise (\<lambda>it. it is empty))" 
proof-
  show "(X is non empty \<longrightarrow> (\<exists>x : set. x in X)) \<and> (\<not> X is non empty \<longrightarrow> (\<exists>x : set. x is empty))"
  proof(intro impI conjI)
    assume [ty]: "X is non empty" 
    then obtain x where
      "x be object" and A1: "x in X" using xboole_0_def_1I by infer_auto
    thus "ex x be set st x in X " using tarski_0_1 by auto
   next
      assume A2: "\<not> X is non empty"
      thus "ex x be set st x is empty " using tarski_0_1 by auto
    qed  
qed infer_auto
print_theorems 
text_raw {*\DefineSnippet{ElementofP}{*}
abbreviation (input) ElementofS :: "(Set \<Rightarrow> Set) \<Rightarrow> (Set \<Rightarrow> Ty)" ("Element-of'' _") where
  "Element-of' F \<equiv> \<lambda>it. Element-of F(it)"
text_raw {*}%EndSnippet*}



lemma Element_of:
  "X is non empty \<Longrightarrow> (x be Element-of X) \<longleftrightarrow> x in X"
  "X is empty \<Longrightarrow> (x be Element-of X) \<longleftrightarrow> x is empty"
  using subset_1_def_1 all_set xboole_0_def_1(1) empty1 by auto

lemma Element_of1:
   "X is non empty \<Longrightarrow> x be Element-of X \<Longrightarrow> x in X" using Element_of(1) by auto

lemma Element_of_rule:
  "x be Element-of {} \<Longrightarrow> x={}" using Element_of empty1 by (intro empty1) infer_auto

lemma Element_of_rule1:
  "{} be Element-of {}" using Element_of empty1 by infer_auto

lemma Element_of_rule2:
  "X be set \<Longrightarrow> X\<noteq> {} \<Longrightarrow> x be Element-of X \<Longrightarrow> x in X"
proof-
  assume A1: "X \<noteq>{}" "x be Element-of X"
  hence "X is non empty" using xboole_0_def_1I empty1 by auto
  thus "x in X" using A1 Element_of by auto
qed

lemma Element_of_rule3:
  "X be set \<Longrightarrow> x in X \<Longrightarrow> x be Element-of X" using xb1[of x X] empty1 Element_of by auto


lemmas Element= Element_of Element_of_rule1 Element_of_rule2 Element_of_rule Element_of_rule3
Element_of(1)[THEN iffD1]


mtheorem sethood_of_Element_of[simp]:
  mlet "X be set"
  "cluster sethood of Element-of X"
proof(standard,cases "X={}")
   assume A1: "X={}"
   show "ex SH being set st (for x be Element-of X holds x in SH)"
     proof(intro bexI[of _"{{}}"] ballI)
        show "{{}} be set" by infer_auto
        fix x
        assume "x be Element-of X"
        hence "x={}" using A1 Element(5) by auto
        thus "x in {{}}" using tarski_def_1 by simp
     qed simp_all
next
assume A1: "X\<noteq>{}"
   show "ex SH being set st (for x be  Element-of X holds x in SH)"
     proof(intro bexI[of _ "X"] ballI impI)
        show "X be set" using all_set by simp
        fix x
        assume [ty]:"x be Element-of X"
        have "X is non empty" using A1 empty1 by auto
        then show "x in X"
            using A1 Element(1)[of X x] by infer_auto
     qed simp_all
qed infer_auto  

abbreviation subset_1_def_2 ("Subset-of _" 105)
where "Subset-of X \<equiv> Element-of (bool X)"

mtheorem subset_1_cl_3:
  mlet "Y be non empty\<bar>set"
  "cluster non empty for Subset-of Y"
proof(standard,standard)
  have "Y in bool Y" using zfmisc_1_def_1[of Y Y ] xboole_0_def_10[of Y Y] by infer_auto
  hence "Y be Element-of (bool Y)" using Element(6) by infer_auto
  thus "Y be non empty\<bar>Subset-of Y" by infer_auto
qed
lemma Subset_of_rule:
  "X \<subseteq> A \<Longrightarrow> X be Subset-of A" using zfmisc_1_def_1[OF all_set all_set]
        Element(6) all_set by auto


lemma Subset_in_rule:
  "X be Subset-of A \<Longrightarrow> X \<subseteq> A"
  using zfmisc_1_def_1 all_set subset_1_cl_1[of A] Element_of[of "bool A" X] by auto

text_raw{*\DefineSnippet{subset_0_def_4}{*}
mdef subset_0_def_4("'(_,_')`") where
    mlet "E be set","A be Subset-of E"
  "func (E,A)` \<rightarrow> Subset-of E equals
     E \\ A"
  text_raw {*}%EndSnippet*}
proof-
   have "E\\A c= E" using xboole_0_def_5 tarski_def_3 by infer_auto
    hence "E\\A in bool E" using zfmisc_1_def_1 by infer_auto
  thus "(E\\A) be Subset-of E" using Element(6) by infer_auto
qed

lemma Subset_trans:
  "A be Subset-of B \<Longrightarrow> B be Subset-of C \<Longrightarrow> A be Subset-of C"
proof-
  assume "A be Subset-of B" "B be Subset-of C"
  hence "A \<subseteq> B" " B\<subseteq> C" using Subset_in_rule by auto
  hence "A \<subseteq> C" using tarski_def_3 all_set by auto
  thus "A be Subset-of C" using Subset_of_rule by auto
qed


mdef subset_1_def_8 ("In '(_ , _')") where
  mlet "x be object","X be set"
  "assume x in X
   func In(x , X) \<rightarrow> Element-of X equals
     x"
proof-
  assume "x in X"
  thus "x be Element-of X" using Element_of_rule3 all_set by auto
qed infer_auto

abbreviation Subset_Family_prefix ("( Subset-Family-of _ )" 105)
where "Subset-Family-of X \<equiv> Subset-of (bool X)"



end
