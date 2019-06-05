theory More_HOL
imports "../Soft_Types/Soft_Types_HOL"

begin

subsection \<open>Notational setup\<close>

text \<open>Get rid of HOL-specific syntax which would conflict with set-theoretic syntax.\<close>

no_notation (ASCII)
  Not ("~ _" [40] 40) and
  conj (infixr "&" 35) and
  disj (infixr "|" 30) and
  implies (infixr "-->" 25) and
  not_equal (infixl "~=" 50)

no_syntax "_Let" :: "[letbinds, 'a] \<Rightarrow> 'a" ("(let (_)/ in (_))" 10)


subsection \<open>Additional logical rules\<close>

lemma disjCI2: "(\<not>A \<Longrightarrow> B) \<Longrightarrow> A \<or> B" by blast

lemma contrapos: "P \<longrightarrow> Q \<Longrightarrow> \<not>Q \<longrightarrow> \<not>P" by blast

lemma ex1_conv1: "(\<exists>!x. P x) \<longleftrightarrow> (\<exists>x. P x) \<and> (\<forall>x x'. P x \<and> P x' \<longrightarrow> x = x')" by blast


end
