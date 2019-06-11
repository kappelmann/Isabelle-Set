section \<open>Structures\<close>

theory Structure
imports Function

begin

(* Experiments implementing structures as set-theoretic functions *)

context
begin



definition monoid where
  "monoid A \<equiv>
    {s \<in> {A, op, e} \<rightarrow> Univ A |
      (e \<in> A) \<and>
      (op \<in> A \<rightarrow> A \<rightarrow> A)
    }"

end

end
