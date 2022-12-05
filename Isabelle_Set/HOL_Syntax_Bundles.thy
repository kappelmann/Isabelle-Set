\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_Syntax_Bundles
  imports HOL.Groups
begin

bundle HOL_order_syntax
begin
notation
  less_eq  ("'(\<le>')") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50) and
  less  ("'(<')") and
  less  ("(_/ < _)"  [51, 51] 50)
notation (input) greater_eq (infix "\<ge>" 50)
notation (input) greater (infix ">" 50)
notation (ASCII)
  less_eq  ("'(<=')") and
  less_eq  ("(_/ <= _)" [51, 51] 50)
notation (input) greater_eq (infix ">=" 50)
notation abs ("\<bar>_\<bar>")
end
bundle no_HOL_order_syntax
begin
no_notation
  less_eq  ("'(\<le>')") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50) and
  less  ("'(<')") and
  less  ("(_/ < _)"  [51, 51] 50)
no_notation (input) greater_eq (infix "\<ge>" 50)
no_notation (input) greater (infix ">" 50)
no_notation (ASCII)
  less_eq  ("'(<=')") and
  less_eq  ("(_/ <= _)" [51, 51] 50)
no_notation (input) greater_eq (infix ">=" 50)
no_notation abs ("\<bar>_\<bar>")
end

bundle HOL_groups_syntax
begin
notation Groups.zero ("0")
notation Groups.one ("1")
notation Groups.plus (infixl "+" 65)
notation Groups.minus (infixl "-" 65)
notation Groups.uminus ("- _" [81] 80)
notation Groups.times (infixl "*" 70)
end
bundle no_HOL_groups_syntax
begin
no_notation Groups.zero ("0")
no_notation Groups.one ("1")
no_notation Groups.plus (infixl "+" 65)
no_notation Groups.minus (infixl "-" 65)
no_notation Groups.uminus ("- _" [81] 80)
no_notation Groups.times (infixl "*" 70)
end


end