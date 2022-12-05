\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Auto2 Setup\<close>
theory Auto2_Setup
imports
  Auto2_HOTG.Auto2_HOTG_Main
  Soft_Types.Soft_Types_HOL
begin

setup \<open>add_backward_prfstep @{thm tballI}\<close>
setup \<open>add_forward_prfstep @{thm tballE}\<close>
(*TODO: no proper support for softly-typed bounded quantifiers yet since
bounded quantifier cases are hard-coded in auto2*)

end