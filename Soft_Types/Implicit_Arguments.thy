theory Implicit_Arguments
  imports Pure
begin

subsection \<open>Implicit_Arguments\<close>

text \<open>
  Two uninterpreted constants that can inject identifiers into the pre-term syntax without
  introducing a variable.
\<close>

consts
  implicit_arg :: "(prop\<Rightarrow>prop) \<Rightarrow> 'a::{}"
  implicit_dummy :: "prop"

syntax
  "_implicit" :: "id_position \<Rightarrow> logic" ("\<implicit>_")
translations
  "\<implicit> x" \<rightleftharpoons> "CONST implicit_arg (\<lambda>x. CONST implicit_dummy)"

ML_file "implicit_arguments.ML"


end