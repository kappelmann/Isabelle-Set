\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Linghan Fang"\<close>
section \<open>Transfinite Recursion\<close>
theory Transfinite_Recursion
  imports
    Functions_Restrict
begin

paragraph \<open>Summary\<close>
text \<open>Translation of transfinite induction from \<^url>\<open>https://en.wikipedia.org/wiki/Transfinite_induction\<close>.
We give the axiomatization of transfinite induction.\<close>


(*TODO: migrate definition from HOL*)
axiomatization transrec :: "((set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a"
  where transrec_eq: "transrec f X = f (fun_restrict (transrec f) X) X"

end
