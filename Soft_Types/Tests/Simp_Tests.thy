section \<open>Simproc Tests\<close>
theory Simp_Tests
  imports "Soft_Types.Soft_Types_HOL"
begin

notepad
begin
  fix A :: bool
  have "A \<Ztypecolon> Bool" by simp
next
  fix x f A B assume [type]: "x \<Ztypecolon> A" "f \<Ztypecolon> A \<Rightarrow> B"
  have "x \<Ztypecolon> A" by simp
  have "f x \<Ztypecolon> B" by simp
end


end
