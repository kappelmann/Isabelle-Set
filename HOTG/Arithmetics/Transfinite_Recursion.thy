\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transfinite Recursion\<close>
theory Transfinite_Recursion
  imports
    Functions_Restrict
begin

(*TODO: migrate definition from HOL*)
axiomatization transrec :: "((set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a"
  where transrec_eq: "transrec f X = f ((transrec f)\<restriction>\<^bsub>X\<^esub>) X"

end
