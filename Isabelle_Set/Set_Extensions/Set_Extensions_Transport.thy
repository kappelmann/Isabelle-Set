\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Transport\<close>
theory Set_Extensions_Transport
  imports
    Set_Extensions_Base
    TBinary_Relations
    Transport.Transport_Bijections
begin

context set_extension
begin

abbreviation (input) "L :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> (=\<^bsub>Rep\<^esub>)"
abbreviation (input) "R :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> (=\<^bsub>Abs\<^esub>)"

lemma bijection_on: "bijection_on (in_field L) (in_field R) l r"
  using inverse_on_Abs_right_left inverse_on_Rep_left_right
  by (intro bijection_onI) auto

sublocale transport? :
  transport_eq_restrict_bijection "mem_of Rep" "mem_of Abs" l r
  rewrites "\<And>S :: set. (=\<^bsub>mem_of S\<^esub>) \<equiv> ((=\<^bsub>S\<^esub>) :: set \<Rightarrow> _)"
  using bijection_on by (intro transport_eq_restrict_bijection.intro) auto

end


end
