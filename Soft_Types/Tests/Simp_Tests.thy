section \<open>Simproc Tests\<close>
theory Simp_Tests
  imports "Soft_Types.Soft_Types_HOL"
begin

notepad
begin
  fix A :: bool
  have "A : Bool" by simp
next
  fix x f A B assume [type]: "x : A" "f : A \<Rightarrow> B"
  have "x : A" by simp
  have "f x : B" by simp
end


end
