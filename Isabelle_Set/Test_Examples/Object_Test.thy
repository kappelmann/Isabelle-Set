theory Object_Test
imports "../Object"

begin

object function "A::set" "B::set"
  is "\<lparr> (graph graph) . \<forall>a \<in> A. \<exists>!b \<in> B. \<langle>a, b\<rangle> \<in> graph \<rparr>"

term "function A B"

end
