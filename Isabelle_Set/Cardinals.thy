\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section\<open>Cardinals\<close>
theory Cardinals
  imports 
    TFunctions
    Ordinals
begin

term bijection_on

definition "card (X :: set) \<equiv> (LEAST i. i : Ord \<and> (\<exists>(f :: set \<Rightarrow> set)(g :: set \<Rightarrow> set). 
  bijection_on X i f g))"



end
