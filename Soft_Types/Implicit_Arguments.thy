section \<open>Implicit Arguments\<close>
theory Implicit_Arguments
  imports Pure
begin

text \<open>Two uninterpreted constants that can inject identifiers into the pre-term
syntax without introducing a variable.\<close>

consts
  implicit_arg :: "(prop \<Rightarrow> prop) \<Rightarrow> 'a :: {}"
  implicit_dummy :: "prop"

syntax
  "_implicit" :: "id_position \<Rightarrow> logic" ("\<implicit>_")
translations
  "\<implicit> x" \<rightleftharpoons> "CONST implicit_arg (\<lambda>x. CONST implicit_dummy)"


abbreviation (input) wildcard :: "'a :: {}" ("?")
  where "? \<equiv> implicit_arg (\<lambda>x. implicit_dummy)"

text \<open>
So we can now write \<^term>\<open>\<implicit>A\<close> as a placeholder for an implicit argument
with name \<open>A\<close>. When we do not want to give a name, we can write \<^term>\<open>?\<close>.
\<close>

ML_file "implicit_arguments.ML"

end
