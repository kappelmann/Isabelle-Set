theory Structure
  imports Equalities
begin


term "\<langle>x, y, z\<rangle>"


structure SemiGroup
fixes
  A : Set
  and op : A \<Rightarrow> A \<Rightarrow> A  (infix "\<cdot>")
  and e : A
  where assoc: "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
  and left_neutral: "e \<cdot> x = x"
  and right_neutral: "x \<cdot> e = x"



text \<open> Internalize the given functions, such that we can tuple them together.
But what users use should be meta-level.

\<close>


text \<open> Gives rise to global operations that carry the class constraint \<close>

definition 
  