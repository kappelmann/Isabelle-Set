section \<open>Setup for Higher-Order Tarski-Grothendieck Set Theory.\<close>

theory Setup
imports "HOL.HOL"
begin

section \<open>Notation\<close>

declare [[eta_contract=false]]

text \<open>Remove conflicting HOL-specific syntax.\<close>

no_notation (ASCII)
  Not ("~ _" [40] 40) and
  conj (infixr "&" 35) and
  disj (infixr "|" 30) and
  implies (infixr "-->" 25) and
  not_equal (infixl "~=" 50)

no_syntax "_Let" :: "[letbinds, 'a] \<Rightarrow> 'a" ("(let (_)/ in (_))" 10)


section \<open>Additional logical rules\<close>

lemma or_if_not_imp: "(\<not>A \<Longrightarrow> B) \<Longrightarrow> A \<or> B" by blast

lemma contrapos: "P \<longrightarrow> Q \<longleftrightarrow> \<not>Q \<longrightarrow> \<not>P" by blast

lemma ex1_iff: "(\<exists>!x. P x) \<longleftrightarrow> (\<exists>x. P x) \<and> (\<forall>x x'. P x \<and> P x' \<longrightarrow> x = x')" by blast


end
