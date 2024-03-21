\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Linghan Fang"\<close>
section \<open>Transfinite Recursion\<close>
theory Transfinite_Recursion
  imports
    Functions_Restrict
begin

paragraph \<open>Summary\<close>
text \<open>We give the axiomatization of transfinite recursion from \<^cite>\<open>ZFC_in_HOL_AFP\<close>,
\<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/ZFC_in_HOL.thy#L1151\<close>.\<close>

axiomatization transrec :: "((set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a"
  where transrec_eq: "transrec f X = f (fun_restrict (transrec f) X) X"

end
