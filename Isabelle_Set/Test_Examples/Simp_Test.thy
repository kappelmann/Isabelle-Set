section \<open>Test cases for the simproc\<close>

theory Simp_Test
  imports "../Isabelle_Set"
begin


setup \<open>soft_type_simp_solver\<close>

notepad
begin

  fix A
  have "A: set" by simp

next

  fix x f A B
  assume [type]:
    "x: element A"
    "f: element A \<Rightarrow> element B"

  have "x: element A" by simp
  have "f x: element B" by simp

end




end
