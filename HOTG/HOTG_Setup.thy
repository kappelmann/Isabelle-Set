\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Setup for Higher-Order Tarski-Grothendieck Set Theory.\<close>
theory HOTG_Setup
  imports
    Transport.HOL_Syntax_Bundles_Base
begin

text \<open>Remove conflicting HOL-specific syntax.\<close>

unbundle no_HOL_ascii_syntax

text \<open>Additional logical rules\<close>

lemma or_if_not_imp: "(\<not>A \<Longrightarrow> B) \<Longrightarrow> A \<or> B" by blast


end
