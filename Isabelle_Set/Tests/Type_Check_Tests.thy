section \<open>Examples for the automatic type derivation procedure.\<close>
theory Type_Check_Tests
  imports
    HOTG.HOTG_Universes
    Isabelle_Set.TSBasics
begin

text \<open>Proving that something is in some universe does not work because the
needed lemmas @{thm "univ_closed_inl" "empty_mem_univ"} are stated using
set-membership.\<close>
lemma "inl {} \<Ztypecolon> Element (univ {})"
  (* by discharge_types *)
oops


end
