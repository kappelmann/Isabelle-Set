section \<open>Elaboration Tests\<close>
theory Elaboration_Tests
  imports "Isabelle_Set.Sets"
begin

declare [[trace_soft_types]]

ML \<open>
  [\<^term>\<open>\<lambda>(x::set). pair\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>\<lambda>(x::set). pair\<close>]
\<close>
ML \<open> Elaboration.elaborate_terms \<^context> [
  \<^term>\<open>{{}}\<close>
]\<close>

ML \<open>
  [\<^term>\<open>{x, y}\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>{x :> Element A, y :> Element A}\<close>]
\<close>

(* This one is pretty underconstrained, since the type of y is not clear *)
ML \<open> Elaboration.elaborate_terms \<^context> [
  \<^term>\<open>\<lambda>y. pair {} y\<close>
]\<close>

ML \<open> Elaboration.elaborate_terms \<^context> [
  \<^term>\<open>\<lambda>x. pair x\<close>
]\<close>


ML \<open> Elaboration.elaborate_terms \<^context> [
  \<^term>\<open>\<lambda>x y. \<langle>x,y\<rangle>\<close>
]\<close>

(*TODO: does not work*)
(* ML \<open>
  [\<^term>\<open>\<langle>x,y\<rangle> = \<langle>y,x\<rangle>\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>\<langle>x :> A, y :> A\<rangle> = \<langle>y,x\<rangle>\<close>]
\<close> *)

text \<open> Transitivity of a relation \<close>

(*TODO: does not work*)
(* ML \<open>
  [\<^term>\<open>\<forall>x y z. \<langle>x, y\<rangle> \<in> r \<longrightarrow> \<langle>y, z\<rangle> \<in> r \<longrightarrow> \<langle>x, z\<rangle> \<in> r\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>\<forall>x y z. \<langle>x, y\<rangle> \<in> (r :> Subset (A \<times> A)) \<longrightarrow> \<langle>y, z\<rangle> \<in> r \<longrightarrow> \<langle>x, z\<rangle> \<in> r\<close>]
\<close> *)


end
