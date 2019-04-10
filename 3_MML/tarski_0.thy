theory tarski_0 imports "../2_Mizar/mizar_reserve" begin

section "TARSKI_0"

text_raw {*\DefineSnippet{tarski-reserve}{*}
reserve x,y,z,a for object
reserve X,Y,Z for set
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{tarski-axiom1}{*}
\<comment>\<open>Set axiom\<close>
theorem tarski_0_1:
  "\<forall>x. x be set" using SET_def by simp
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{tarski-set-exists}{*}
theorem set_exists[ex]: "inhabited(set)"
  using tarski_0_1 inhabited_def by auto
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{tarski-axiom2}{*}
\<comment>\<open>Extensionality axiom\<close>
axiomatization where tarski_0_2:
  "\<forall>X. \<forall>Y. (\<forall>x. x in X \<longleftrightarrow> x in Y)
    \<longrightarrow> X = Y"
text_raw {*}%EndSnippet*}
  lemmas tarski_0_2a = tarski_0_2[THEN bspec,THEN bspec,rule_format,OF _ _ _ _ ballI,simplified]

text_raw {*\DefineSnippet{tarski-axiom3}{*}
\<comment>\<open>Axiom of pair\<close>
axiomatization where tarski_0_3:
  "\<forall>x. \<forall>y. \<exists>Z. \<forall>a.
      a in Z \<longleftrightarrow> a = x \<or> a = y"
text_raw {*}%EndSnippet*}

thm tarski_0_3
text_raw {*\DefineSnippet{tarski-axiom4}{*}
\<comment>\<open>Axiom of union\<close>
axiomatization where tarski_0_4:
  "\<forall>X. \<exists>Z. \<forall>x.
     x in Z \<longleftrightarrow> (\<exists>Y. x in Y \<and> Y in X)"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{tarski-axiom5}{*}
\<comment>\<open>Axiom of regularity\<close>
axiomatization where tarski_0_5:
  "\<forall>x. \<forall>X. x in X \<longrightarrow> (\<exists>Y. Y in X \<and>
     \<not>(\<exists>z. z in X \<and> z in Y))"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{tarski-axiom6}{*}
\<comment>\<open>Fraenkel's scheme\<close>
axiomatization where tarski_0_sch_1:
  "A be set \<Longrightarrow>
     \<forall>x,y,z. P(x,y) \<and> P(x,z) \<longrightarrow> y = z \<Longrightarrow>
       \<exists>X. \<forall>x.
   x in X \<longleftrightarrow> (\<exists>y. y in A \<and> P(y,x))"
text_raw {*}%EndSnippet*}

end