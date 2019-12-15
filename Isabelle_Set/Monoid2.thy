section \<open>Monoids\<close>

text \<open>
  We define monoids as a soft type class and experiment with how it interacts
  with implicit arguments and type inference.
\<close>

theory Monoid2
imports Structures2

begin

definition [typedef]: "Monoid A = Zero A \<bar> Plus A \<bar>
  type (\<lambda>M.
    (\<forall>x\<in> A.
      plus M (zero M) x = x \<and>
      plus M x (zero M) = x) \<and>
    (\<forall>x y z \<in> A.
      plus M (plus M x y) z = plus M x (plus M y z))
  )"

text \<open>It would be really nice if this worked:\<close>

declare [[auto_elaborate]]
lemma Monoid_typeI:
  assumes "M : Zero A"
          "M : Plus A"
          "\<And>x. x \<in> A \<Longrightarrow> 0 + x = x"
          "\<And>x. x \<in> A \<Longrightarrow> x + 0 = x"
          "\<And>x y z. \<lbrakk>x \<in> A; y \<in> A; z \<in> A\<rbrakk> \<Longrightarrow> (x + y) + z = x + y + z"
  shows "M : Monoid A"
  unfolding Monoid_def
  apply unfold_types
  apply auto \<comment>\<open>Doesn't use the assumptions as they weren't elaborated correctly\<close>
  using assms
oops
declare [[auto_elaborate=false]]

text \<open>Instead we have to do this for now:\<close>

lemma Monoid_typeI:
  assumes "M : Zero A"
          "M : Plus A"
          "\<And>x. x \<in> A \<Longrightarrow> plus M (zero M) x = x"
          "\<And>x. x \<in> A \<Longrightarrow> plus M x (zero M) = x"
          "\<And>x y z. \<lbrakk>x \<in> A; y \<in> A; z \<in> A\<rbrakk>
            \<Longrightarrow> plus M (plus M x y) z = plus M x (plus M y z)"
  shows "M : Monoid A"
  unfolding Monoid_def by unfold_types (auto intro: assms)


subsection \<open>Direct sum\<close>

text \<open>
  In this section we develop the structure constructor for direct sums of
  monoids, by defining it as the (disjoint) structure union of the zero and plus
  pair structures.

  We emulate automation that needs to be implemented in future work.
\<close>

definition "Zero_Pair Z1 Z2 = object {\<langle>@zero, \<langle>zero Z1, zero Z2\<rangle>\<rangle>}"

(*These should be automatically generated*)
lemma Zero_Pair_fields [simp]: "object_fields (Zero_Pair Z1 Z2) = {@zero}"
  unfolding Zero_Pair_def by auto

lemma Zero_Pair_zero [simp]: "(Zero_Pair Z1 Z2) @@ zero = \<langle>zero Z1, zero Z2\<rangle>"
  unfolding Zero_Pair_def by simp

definition "Plus_Pair A B P1 P2 = object {
  \<langle>@plus, \<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle>\<in> A \<times> B. \<langle>plus P1 a1 a2, plus P2 b1 b2\<rangle>\<rangle>}"

(*Should be automatically generated*)
lemma Plus_Pair_fields [simp]: "object_fields (Plus_Pair A B P1 P2) = {@plus}"
  unfolding Plus_Pair_def by auto

lemma Plus_Pair_plus [simp]:
  "(Plus_Pair A B P1 P2) @@ plus =
    \<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle>\<in> A \<times> B. \<langle>plus P1 a1 a2, plus P2 b1 b2\<rangle>"
  unfolding Plus_Pair_def by simp

(*Monoid direct sum is the composition of the respective zero and pair instances*)
definition "Monoid_Sum A B M1 M2 = Zero_Pair M1 M2 [+] Plus_Pair A B M1 M2"

(*Should be automatically generated*)
lemma [simp]:
  shows
    Monoid_Sum_zero: "(Monoid_Sum A B M1 M2) @@ zero = (Zero_Pair M1 M2) @@ zero"
  and
    Monoid_Sum_plus: "(Monoid_Sum A B M1 M2) @@ plus = (Plus_Pair A B M1 M2) @@ plus"
  unfolding Monoid_Sum_def
  (*The level of abstraction needed in this proof requires structure composition
    to be properly set up*)
  subgoal
  apply (subst object_composition_selector)
    apply simp
      apply (rule equalityI)
        apply simp
        apply (elim conjE)
        apply simp
        apply string_neq
      apply simp
    apply simp
  done
  subgoal
  apply (subst object_composition_selector)
    apply simp
      apply (rule equalityI)
        apply simp
        apply (elim conjE)
        apply simp
        apply string_neq
      apply simp
    apply simp
      apply (rule impI, rule ccontr)
      apply string_neq
  done
done

text \<open>
  The following proofs illustrate that reasoning with types is still very
  pedestrian and needs better automated support.
\<close>

lemma Zero_Pair_type [type]:
  "Zero_Pair : Zero A \<Rightarrow> Zero B \<Rightarrow> Zero (A \<times> B)"
  unfolding Zero_Pair_def
  by unfold_types (auto simp: zero_def)

lemma Plus_Pair_type [type]:
  "Plus_Pair : (A : set) \<Rightarrow> (B : set) \<Rightarrow> Plus A \<Rightarrow> Plus B \<Rightarrow> Plus (A \<times> B)"
  unfolding Plus_Pair_def plus_def
  by (unfold_types, auto intro!: FunctionE) auto
  (*We really shouldn't have to intro! FunctionE here...*)

lemma Monoid_Sum_type [type]:
  "Monoid_Sum : (A : set) \<Rightarrow> (B : set) \<Rightarrow> Monoid A \<Rightarrow> Monoid B \<Rightarrow> Monoid (A \<times> B)"
  apply (intro typeI)
  apply (intro Monoid_typeI Zero_typeI Plus_typeI)
sorry


lemma [type_instance]:
  "M1 : Plus A \<Longrightarrow> M2 : Plus B \<Longrightarrow> Plus_Pair A B M1 M2 : Plus (A \<times> B)"
  "M1 : Zero A \<Longrightarrow> M2 : Zero B \<Longrightarrow> Zero_Pair M1 M2 : Zero (A \<times> B)"
  "M1 : Monoid A \<Longrightarrow> M2 : Monoid B \<Longrightarrow> Monoid_Sum A B M1 M2 : Monoid (A \<times> B)"
  by discharge_types


subsection \<open>Overloaded syntax\<close>

context
  notes [[auto_elaborate, trace_soft_types]]
begin

lemma "x + 0 = x"
  print_types
  oops

lemma "\<langle>x, y\<rangle> + 0 = \<langle>x, y\<rangle>"
  print_types
  oops

lemma "x + (y + z) = x + y + z"
  print_types
  oops

lemma "x + y = z + w \<and> u + v = 0"
  print_types
  oops

end


subsection \<open>Extension to groups\<close>

definition [typedef]: "Group A = Monoid A \<bar>
  type (\<lambda>G.
    G @@ inv \<in> A \<rightarrow> A \<and>
    (\<forall>x\<in> A. plus G x (G@@inv `x) = zero G) \<and>
    (\<forall>x\<in> A. plus G (G@@inv `x) x = zero G)
  )"

lemma group_is_monoid:  "G : Group A \<Longrightarrow> G : Monoid A"
  unfolding Group_def by (fact Int_typeE1)


end
