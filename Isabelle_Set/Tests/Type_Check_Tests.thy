section \<open>Examples for the automatic type derivation procedure.\<close>
theory Type_Check_Tests
  imports "Isabelle_Set.Sets"
begin

text \<open>Proving that something is in some universe does not work because the
needed lemmas @{thm "univ_closed_inl" "empty_mem_univ"} are stated using
set-membership.\<close>
lemma "inl {} : Element (univ {})"
  (* by discharge_types *)
oops


end
