theory group_2
imports group_1
begin

reserve x for object
reserve G for Group
reserve A for "Subset-of-struct G"

text_raw {*\DefineSnippet{group2def1}{*}
mdef group_2_def_1 (infix "\<hungarumlaut>\<^sup>-\<^sup>1 \<^sub>" 150) where
mlet "A be Subset-of-struct G"
 "func A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<rightarrow> Subset-of-struct G equals
     {g\<^sup>-\<^sup>1\<^sub>G where g be Element-of-struct G : g in A}"
text_raw {*}%EndSnippet*}
proof-
  let ?F = "{g\<^sup>-\<^sup>1\<^sub>G where g be Element-of-struct G:g in A}"
  have "?F \<subseteq> the carrier of G"
  proof(intro tarski_def_3I,auto)
    fix x assume A1:"x in ?F"
    then obtain g where
      [ty]:"g be (Element-of-struct G)" and
      A1: "x= g\<^sup>-\<^sup>1\<^sub>G" "g in A" using Fraenkel_A1_ex[OF _ _ A1] by auto
    have C1: "the carrier of G is non empty" using Subset_in_rule A1 xboole_0_def_1I by auto
    thus "x in_struct G" using Element(1)[of "the carrier of G" x]   A1(1) by mauto
  qed
  thus "?F be (Subset-of-struct G)" using Subset_of_rule by simp
qed

mtheorem group_2_def_1_involutiveness:
  "
  for B be Subset-of-struct G st B = A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G holds A = B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
proof(rule ballI,rule impI)
  fix B assume T0[ty]:"B be (Subset-of-struct G)" and
            A0:"B = A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
  hence T1:"A \<subseteq> the carrier of G" using Subset_in_rule group_2_def_1[of G B] by auto
  have S: "sethood_prop(Element-of-struct G)" by mauto
  show "A = B \<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
  proof (unfold xboole_0_def_10[OF all_set all_set],rule conjI)
    show "A \<subseteq> B \<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
    proof(standard,auto)
      fix a assume A1: "a in A"
      have C1: "the carrier of G is non empty" by mauto
      have T2[ty]: "a be (Element-of-struct G)" using A1 T1 tarski_def_3E[of A "the carrier of G"] 
                           Element(6)[of "the carrier of G"] by auto
      hence T3: "a \<^sup>-\<^sup>1\<^sub>G be (Element-of-struct G)" using group_1_def_5 by mauto
      have A2: "(a \<^sup>-\<^sup>1\<^sub>G) \<^sup>-\<^sup>1\<^sub>G = a" using group_1_def_5_involutiveness by auto
      have "a \<^sup>-\<^sup>1\<^sub>G in B" using Fraenkel_A1_in[OF S T2, of "\<lambda>g. g in A" " \<lambda>g. g\<^sup>-\<^sup>1\<^sub>G"] A1 group_2_def_1 A0 by auto
      thus "a in B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" using A2 Fraenkel_A1_in[OF S T3, of "\<lambda>g. g in B" " \<lambda>g.  g\<^sup>-\<^sup>1\<^sub>G"] group_2_def_1 by mauto
    qed mauto
    show "B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<subseteq> A "
    proof(standard,auto)
      fix a assume A1: "a in B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
      hence A3: "a in {g\<^sup>-\<^sup>1\<^sub>G where g be Element-of-struct G:g in B}" using group_2_def_1[of G B] by auto
      obtain b where
         [ty]: "b be (Element-of-struct G)" and A4:"a = b\<^sup>-\<^sup>1\<^sub>G" " b in B" using group_2_def_1 Fraenkel_A1_ex[OF _ _ A3] by mauto
      hence A5: "b in {g\<^sup>-\<^sup>1\<^sub>G where g be Element-of-struct G:g in A}" using A0 group_2_def_1[of G A] by auto
      obtain c where
         [ty]: "c be (Element-of-struct G)" and "b = c\<^sup>-\<^sup>1\<^sub>G" " c in A" using group_2_def_1 Fraenkel_A1_ex[OF _ _ A5] by mauto
      thus "a in A" using group_1_def_5_involutiveness A4 by auto
    qed mauto
  qed
qed auto

mtheorem group_2_th_2:
  mlet "A be Subset-of-struct G"
  "x in A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<longleftrightarrow> (ex g be Element-of-struct G st x = g\<^sup>-\<^sup>1\<^sub>G \<and> g in A)"
proof(rule iffI3)
  show " x in A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<longrightarrow> (ex g be Element-of-struct G st x = g\<^sup>-\<^sup>1\<^sub>G \<and> g in A)"
    using Fraenkel_A1_ex group_2_def_1 by auto
  assume "ex g be Element-of-struct G st x = g\<^sup>-\<^sup>1\<^sub>G \<and> g in A"
  then obtain g where
    T1: "g be Element-of-struct G" and A1:"x = g\<^sup>-\<^sup>1\<^sub>G \<and> g in A" by auto
  show "x in A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" using group_2_def_1 Fraenkel_A1_in[OF _ T1]
     using A1 by auto
 qed

theorem group_2_th_2a:
 assumes [ty]:"G is Group"
    "A is Subset-of-struct G"
    "a is Element-of-struct G"
    and "a in A"
shows "a\<^sup>-\<^sup>1\<^sub>G in A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
proof-
  have I: "inhabited(Element-of-struct G)" by auto
  hence "ex c be Element-of-struct G st a\<^sup>-\<^sup>1\<^sub>G = c\<^sup>-\<^sup>1\<^sub>G \<and> c in A" using assms ty by blast
  thus ?thesis using group_2_th_2 by mauto
qed

reserve g,h for "Element-of-struct G"  
  
text_raw {*\DefineSnippet{group_2_th_3}{*}
mtheorem group_2_th_3:
   "{g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G = {g\<^sup>-\<^sup>1\<^sub>G}"
text_raw {*}%EndSnippet*}
proof(intro xboole_0_def_10I conjI)
  have [ty]:"bool the' carrier(G) is set " by mauto
  show [ty]: "{g} \<hungarumlaut>\<^sup>-\<^sup>1\<^sub> G is set" using subset_1_def_1_ty_parent by mauto
  show [ty]: "{ g\<^sup>-\<^sup>1\<^sub>G} is set" using subset_1_def_1_ty_parent by mauto

  show "{g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<subseteq> { g\<^sup>-\<^sup>1\<^sub>G}"
  proof(standard,auto)
    fix x assume "x in {g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
    then obtain a where [ty]:"a be Element-of-struct G" and
      A1:"x = a\<^sup>-\<^sup>1\<^sub>G" and
      A2:"a in {g}" using group_2_th_2 by mauto
    have "a=g" using A2 tarski_def_1 by simp
    thus "x in { g\<^sup>-\<^sup>1\<^sub>G}" using tarski_def_1 A1 by auto
  qed mauto
  show "{g\<^sup>-\<^sup>1\<^sub>G} \<subseteq> {g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
  proof(standard,auto)
    fix x assume "x in {g\<^sup>-\<^sup>1\<^sub>G}"
    hence A3: "x = g\<^sup>-\<^sup>1\<^sub>G" using tarski_def_1 by auto
    have "g in {g}" using tarski_def_1 by auto
    thus "x in {g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" using A3 group_2_th_2a[of G "{g}" g] by mauto
  qed mauto
qed mauto

text_raw {*\DefineSnippet{group_2_th_4}{*}
mtheorem group_2_th_4:
  "{h, g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G = {h\<^sup>-\<^sup>1\<^sub>G, g\<^sup>-\<^sup>1\<^sub>G}"
text_raw {*}%EndSnippet*}
proof(intro xboole_0_def_10I)
  have [ty]:"bool the' carrier(G) is set " by mauto
show "{h, g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G is set" using subset_1_def_1_ty_parent by mauto
show "{h\<^sup>-\<^sup>1\<^sub>G, g\<^sup>-\<^sup>1\<^sub>G} is set" using subset_1_def_1_ty_parent by mauto
  show "{h, g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<subseteq> {h\<^sup>-\<^sup>1\<^sub>G, g\<^sup>-\<^sup>1\<^sub>G}"
  proof(standard,auto)
     fix x assume "x in {h, g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
    then obtain a where T2[ty]:"a be Element-of-struct G" and
      A1:"x = a\<^sup>-\<^sup>1\<^sub>G" and
      A2:"a in {h, g}" using group_2_th_2 by mauto
    have "a=h \<or> a=g" using A2 tarski_def_2 by simp
    thus "x in {h\<^sup>-\<^sup>1\<^sub>G, g\<^sup>-\<^sup>1\<^sub>G}" using A1 tarski_def_2 by auto
  qed mauto
  show "{h\<^sup>-\<^sup>1\<^sub>G, g\<^sup>-\<^sup>1\<^sub>G} \<subseteq> {h, g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
  proof(standard,auto)
    fix x assume "x in {h\<^sup>-\<^sup>1\<^sub>G, g\<^sup>-\<^sup>1\<^sub>G}"
    hence A3: "x = g\<^sup>-\<^sup>1\<^sub>G \<or> x = h\<^sup>-\<^sup>1\<^sub>G" using tarski_def_2 by auto
    have I: "inhabited(Element-of-struct G)" by auto
    have "g in {h,g} \<and> h in {h,g}" using tarski_def_2 by auto
    thus "x in {h, g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" using A3 group_2_th_2a[of G "{h,g}"] by mauto
  qed mauto
qed mauto

text_raw {*\DefineSnippet{group2def2}{*}
mdef group_2_def_2("_  \<Otimes>\<^sub>_ _" [66, 1000, 67] 66) where
  mlet "G be Group", "A be Subset-of-struct G","B be Subset-of-struct G"
  "func A \<Otimes>\<^sub>G B \<rightarrow> Subset-of-struct G equals
     {a \<otimes>\<^sub>G b where a be Element-of-struct G,
                     b be Element-of-struct G : a in A \<and> b in B}"
text_raw {*}%EndSnippet*}
proof-
  let ?F = " {a \<otimes>\<^sub>G b where a be Element-of-struct G, b be Element-of-struct G :a in A \<and> b in B}"
  have "?F \<subseteq> the carrier of G"
  proof(standard,auto)
    fix x assume A1:"x in ?F"
    obtain a b where
      [ty]: "a be Element-of-struct G" "b be Element-of-struct G" and
      A1: "x=  a \<otimes>\<^sub>G b" "a in A \<and> b in B" using Fraenkel_A2_ex[OF _ _ _ _ A1] by auto
    have C1: "the carrier of G is non empty" using A1(2) xboole_0_def_1I by auto
    thus "x in_struct G" using Element(7) A1 by mauto
  qed
  thus "?F be Subset-of-struct G" using Subset_of_rule by simp
qed


theorem group_2_th_8[THEN bspec,THEN bspec,THEN bspec,rule_format]:
  "for G be Group, A, B be Subset-of-struct G holds
      x in A \<Otimes>\<^sub>G B \<longleftrightarrow> (ex a,b be Element-of-struct G st x = a \<otimes>\<^sub>G b \<and> a in A \<and> b in B)"
proof(intro ballI,rule iffI3)
  fix G A B
  assume T0[ty]: "G be Group" "A be (Subset-of-struct G)" "B be (Subset-of-struct G)"
  show "x in A \<Otimes>\<^sub>G B \<longrightarrow> (ex a,b be Element-of-struct G st x = a \<otimes>\<^sub>G b \<and> a in A \<and> b in B)"
    using Fraenkel_A2_ex group_2_def_2 by mauto
  assume "ex a,b be Element-of-struct G st x = a \<otimes>\<^sub>G b \<and> a in A \<and> b in B"
  then obtain a b where
    T1[ty]: "a be Element-of-struct G" "b be Element-of-struct G" and A1:"x = a \<otimes>\<^sub>G b" and A2:"a in A \<and> b in B" by auto
  show "x in A \<Otimes>\<^sub>G B" using group_2_def_2
       Fraenkel_A2_in[of "Element-of-struct G" "Element-of-struct G" a b "\<lambda>a b. a in A \<and> b in B" ]
     using A1 A2 by mauto
qed auto

theorem group_2_th_8a:
 assumes [ty]:"G is Group"
    "A is Subset-of-struct G"
    "B is Subset-of-struct G"
    "a is Element-of-struct G"
    "b is Element-of-struct G"
    and "a in A" "b in B"
shows "a \<otimes>\<^sub>G b in A \<Otimes>\<^sub>G B"
proof-
  have I: "inhabited(Element-of-struct G)" by auto
  hence "ex c,d be Element-of-struct G st a \<otimes>\<^sub>G b = c \<otimes>\<^sub>G d \<and> c in A \<and> d in B" using assms(6,7) ty by blast
  thus ?thesis using group_2_th_8[of G A B] by mauto
qed

text_raw {*\DefineSnippet{group_2_th_11}{*}
theorem group_2_th_11:
  assumes[ty]: "G be Group"
          "A be Subset-of-struct G" "B be Subset-of-struct G"
  shows "(A \<Otimes>\<^sub>G B) \<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G = B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<Otimes>\<^sub>G A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
text_raw {*}%EndSnippet*}
proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
  have [ty]:"bool the' carrier(G) is set " by mauto  
  show "(A \<Otimes>\<^sub>G B) \<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<subseteq> B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<Otimes>\<^sub>G A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
  proof(standard,auto)
    have I: "(inhabited(Subset-of (the' carrier)(G)))"
            "(inhabited(Element-of (the' carrier)(G)))" by auto
      fix x
      assume "x in (A \<Otimes>\<^sub>G B) \<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
      then obtain g where
        T2[ty]: "g be Element-of-struct G" and A1:"x = g\<^sup>-\<^sup>1\<^sub>G" "g in A \<Otimes>\<^sub>G B" using group_2_th_2 by mauto
      obtain g1 g2 where
        T3[ty]:"g1 be Element-of-struct G" "g2 be Element-of-struct G" and A2: "g = g1 \<otimes>\<^sub>G g2" "g1 in A \<and> g2 in B"
           using A1 group_2_th_8 by auto
      have A5: "g1\<^sup>-\<^sup>1\<^sub>G in A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G " " g2\<^sup>-\<^sup>1\<^sub>G in B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" using group_2_th_2a[of G A "g1" ]
          group_2_th_2a[of G B "g2" ] A2 by auto
      have "x = g2\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G g1\<^sup>-\<^sup>1\<^sub>G" using group_1_th_16 A1 A2 by auto
      thus "x in B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<Otimes>\<^sub>G A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" using A5 group_2_th_8a[of G "B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" "A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"] by mauto
    qed mauto
  show "B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<Otimes>\<^sub>G A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<subseteq> (A \<Otimes>\<^sub>G B) \<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
    proof(standard,auto)
      fix x
      assume "x in B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<Otimes>\<^sub>G A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
      then obtain h2 h1 where
        [ty]:"h2 be Element-of-struct G" "h1 be Element-of-struct G"
         and A1: "x = h2 \<otimes>\<^sub>G h1" "h2 in B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<and> h1 in A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" using group_2_th_8 by mauto
      obtain g1 where
        [ty]: "g1 be Element-of-struct G" and A2:"h1 = g1\<^sup>-\<^sup>1\<^sub>G" "g1 in A" using group_2_th_2 A1 by auto
      obtain g2 where
        [ty]: "g2 be Element-of-struct G" and A3:"h2 = g2\<^sup>-\<^sup>1\<^sub>G" "g2 in B" using group_2_th_2 A1 by auto
      have A4: "g1 \<otimes>\<^sub>G g2 in A \<Otimes>\<^sub>G B" using group_2_th_8a[of G A B g1 g2] A2 A3 by auto
      have "x = (g1 \<otimes>\<^sub>G g2)\<^sup>-\<^sup>1\<^sub>G" using group_1_th_16 A1 A2 A3 by auto
      thus "x in (A \<Otimes>\<^sub>G B) \<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" using group_2_th_2a[of G "A \<Otimes>\<^sub>G B"] A2 A3 A4 by mauto
    qed mauto
  qed

reserve G for "Group"
reserve A,B,C for "Subset-of-struct G"
reserve a,b,g,g1,g2,h,h1,h2 for "Element-of-struct G"

(* KP: To twierdzenie ma inny numer w mojej wersji? I jest dla non-empty multMagma? *)
text_raw {*\DefineSnippet{group_2_th_19}{*}
mtheorem group_2_th_19:
  "{g1,g2} \<Otimes>\<^sub>G {h1,h2} =
     {g1 \<otimes>\<^sub>G h1,g1 \<otimes>\<^sub>G h2 ,g2 \<otimes>\<^sub>G h1 ,g2 \<otimes>\<^sub>G h2 }"
  text_raw {*}%EndSnippet*}
proof(intro xboole_0_def_10I)
  have [ty]:"bool the' carrier(G) is set " by mauto
  show "({g1,g2} \<Otimes>\<^sub>G {h1,h2}) is set" by mauto
  show "({g1 \<otimes>\<^sub>G h1,g1 \<otimes>\<^sub>G h2 ,g2 \<otimes>\<^sub>G h1 ,g2 \<otimes>\<^sub>G h2 }) is set" by mauto
  show "{g1,g2}  \<Otimes>\<^sub>G {h1,h2} \<subseteq> {g1 \<otimes>\<^sub>G h1,g1 \<otimes>\<^sub>G h2 ,g2 \<otimes>\<^sub>G h1 ,g2 \<otimes>\<^sub>G h2 }"
  proof(standard,auto)
    fix x assume "x in {g1,g2}  \<Otimes>\<^sub>G {h1,h2}"
    then obtain a b where T2:"a be Element-of-struct G" "b be Element-of-struct G" and
      A1:"x = a \<otimes>\<^sub>G b" and
      A2:"a in {g1, g2} \<and> b in {h1,h2}" using group_2_th_8 by mauto
    have "a=g1 \<or> a=g2" "b=h1 \<or> b=h2" using A2 tarski_def_2 by auto
    thus "x in {g1 \<otimes>\<^sub>G h1,g1 \<otimes>\<^sub>G h2 ,g2 \<otimes>\<^sub>G h1 ,g2 \<otimes>\<^sub>G h2 }" using A1 enumset1_def_2 by auto
  qed mauto
  show "{g1 \<otimes>\<^sub>G h1,g1 \<otimes>\<^sub>G h2 ,g2 \<otimes>\<^sub>G h1 ,g2 \<otimes>\<^sub>G h2 } \<subseteq> {g1,g2}  \<Otimes>\<^sub>G {h1,h2}"
  proof(standard,auto)
    fix x assume "x in {g1 \<otimes>\<^sub>G h1,g1 \<otimes>\<^sub>G h2 ,g2 \<otimes>\<^sub>G h1 ,g2 \<otimes>\<^sub>G h2 }"
    hence A3: "x = g1 \<otimes>\<^sub>G h1 \<or> x = g1 \<otimes>\<^sub>G h2 \<or> x = g2 \<otimes>\<^sub>G h1 \<or> x = g2 \<otimes>\<^sub>G h2" using enumset1_def_2 by auto
    have "g1 in {g1,g2} \<and> g2 in {g1,g2}" "h1 in {h1,h2} \<and> h2 in {h1,h2}" using tarski_def_2 by auto
    thus "x in {g1,g2}  \<Otimes>\<^sub>G {h1,h2}" using A3 group_2_th_8a[of G "{g1,g2}" "{h1,h2}"] by mauto
  qed mauto
qed mauto

end
