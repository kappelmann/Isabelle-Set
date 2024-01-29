\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transfinite Recursion\<close>
theory Transfinite_Recursion
  imports
    Functions_Restrict
begin

section \<open>

\<close>

(*TODO: migrate definition from HOL*)
axiomatization transrec :: "((set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a"
  where transrec_eq: "transrec f X = f (fun_restrict (transrec f) X) X"

end
