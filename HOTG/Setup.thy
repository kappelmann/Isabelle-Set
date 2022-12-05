\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Setup for Higher-Order Tarski-Grothendieck Set Theory.\<close>
theory Setup
  imports HOL.HOL
begin

subsection \<open>Notation\<close>

declare [[eta_contract=false]]

text \<open>Remove conflicting HOL-specific syntax.\<close>

bundle HOL_ascii_syntax
begin
notation (ASCII)
  Not ("~ _" [40] 40) and
  conj (infixr "&" 35) and
  disj (infixr "|" 30) and
  implies (infixr "-->" 25) and
  not_equal (infixl "~=" 50)
syntax "_Let" :: "[letbinds, 'a] \<Rightarrow> 'a" ("(let (_)/ in (_))" 10)
end
bundle no_HOL_ascii_syntax
begin
no_notation (ASCII)
  Not ("~ _" [40] 40) and
  conj (infixr "&" 35) and
  disj (infixr "|" 30) and
  implies (infixr "-->" 25) and
  not_equal (infixl "~=" 50)
no_syntax "_Let" :: "[letbinds, 'a] \<Rightarrow> 'a" ("(let (_)/ in (_))" 10)
end

unbundle no_HOL_ascii_syntax

subsection \<open>Additional logical rules\<close>

lemma or_if_not_imp: "(\<not>A \<Longrightarrow> B) \<Longrightarrow> A \<or> B" by blast


end
