section \<open>Monoids\<close>

text \<open>
  We define monoids as a soft type class (though without tool support) and
  experiment with how it interacts with implicit arguments and type inference.
\<close>

theory Monoid2
imports Structures2

begin

declare [[auto_elaborate=false, trace_soft_types]]

definition [typedef]:
  "Monoid A =
    Zero A \<bar> Plus A \<bar>
    type (\<lambda>struct.
      (\<forall>x\<in> A.
        plus struct (zero struct) x = x \<and>
        plus struct x (zero struct) = x) \<and>
      (\<forall>x y z \<in> A.
        plus struct (plus struct x y) z = plus struct x (plus struct y z))
    )"

lemma Monoid_is_Zero [derive]: "M : Monoid A \<Longrightarrow> M: Zero A"
  by unfold_types

lemma Monoid_is_Plus [derive]: "M : Monoid A \<Longrightarrow> M : Plus A"
  by unfold_types

lemma Monoid_typeI:
  assumes "struct : Zero A"
          "struct : Plus A"
          "\<And>x. x \<in> A \<Longrightarrow> plus struct x (zero struct) = x"
          "\<And>x. x \<in> A \<Longrightarrow> plus struct (zero struct) x = x"
          "\<And>x y z. \<lbrakk>x \<in> A; y \<in> A; z \<in> A\<rbrakk> \<Longrightarrow>
            plus struct (plus struct x y) z = plus struct x (plus struct y z)"
  shows "struct : Monoid A"
  using assms by unfold_types auto

text \<open>
  Now we define the global operations as projections. Here, we also convert the
  set functions to meta functions. The axioms can then be derived.
\<close>

lemma
  assumes "M : Monoid A"
  shows
    monoid_left_neut [simp]: "x \<in> A \<Longrightarrow> plus M (zero M) x = x" and
    monoid_right_neut [simp]: "x \<in> A \<Longrightarrow> plus M x (zero M) = x" and
    monoid_assoc [simp]: "\<lbrakk>x \<in> A; y \<in> A; z \<in> A\<rbrakk>
      \<Longrightarrow> plus M (plus M x y) z = plus M x (plus M y z)"

  using assms plus_def zero_def by unfold_types blast+


subsection \<open>Instance for pairs\<close>

definition "pair_plus A B p1 p2 =
  {\<langle>@plus, \<lambda>\<langle>a1,b1\<rangle>\<in>A\<times>B. \<lambda>\<langle>a2,b2\<rangle>\<in>A\<times>B. \<langle>plus p1 a1 a2, plus p2 b1 b2\<rangle>\<rangle>}"

definition "pair_zero z1 z2 = {\<langle>@zero, \<langle>zero z1, zero z2\<rangle>\<rangle>}"

(*
  TODO: Need some form of structure composition
    "pair_monoid = pair_zero [+] pair_plus"
*)
definition "pair_monoid A B m1 m2 \<equiv> {
  \<langle>@zero, (pair_zero m1 m2) @@ zero\<rangle>,
  \<langle>@plus, (pair_plus A B m1 m2) @@ plus\<rangle>
}"

lemma pair_monoid_zero [simp]:
  "(pair_monoid A B m1 m2)@@zero = (pair_zero m1 m2)@@zero"
  unfolding pair_monoid_def by simp

lemma pair_monoid_plus [simp]:
  "(pair_monoid A B m1 m2)@@plus = (pair_plus A B m1 m2)@@plus"
  unfolding pair_monoid_def by simp

text \<open>
  The following proofs illustrate that reasoning with types is still very
  pedestrian and needs better automated support.
\<close>

lemma pair_plus_plus [simp]:
  "(pair_plus A B p1 p2)@@plus =
    \<lambda>\<langle>a1,b1\<rangle>\<in> A\<times>B. \<lambda>\<langle>a2,b2\<rangle>\<in> A\<times>B. \<langle>plus p1 a1 a2, plus p2 b1 b2\<rangle>"
  unfolding pair_plus_def by simp

lemma pair_plus_type [type]:
  "pair_plus : (A : set) \<Rightarrow> (B : set) \<Rightarrow> Plus A \<Rightarrow> Plus B \<Rightarrow> Plus (A \<times> B)"
  oops

lemma pair_zero_type [type]:
  "pair_zero : Zero A \<Rightarrow> Zero B \<Rightarrow> Zero (A \<times> B)"
  unfolding Zero_def pair_zero_def zero_def
  by unfold_types simp

lemma pair_monoid_type [type]:
  "pair_monoid : (A : set) \<Rightarrow> (B : set) \<Rightarrow> Monoid A \<Rightarrow> Monoid B \<Rightarrow> Monoid (A \<times> B)"
proof (intro Pi_typeI)

  fix A B p1 p2 assume [type]: "A : set" "B : set" "p1 : Monoid A" "p2 : Monoid B"
  let ?plus = "(pair_monoid A B p1 p2)[@plus]"
  let ?zero = "(pair_monoid A B p1 p2)[@zero]"

  show "pair_monoid A B p1 p2 : Monoid (A \<times> B)"
  proof (rule Monoid_typeI)

    show "pair_monoid A B p1 p2 : Zero (A \<times> B)"
      by (rule Zero_typeI) auto
    show "pair_monoid A B p1 p2 : Plus (A \<times> B)"
      by (rule Plus_typeI) auto

    show "\<forall>x: element (A \<times> B). ?plus `?zero `x = x"
      unfolding split_paired_Ball
        (*^This should be unnecessary now with the soft type translation*)
      by (auto simp: pair_plus_def pair_zero_def)

    show "\<forall>x: element (A \<times> B). ?plus `x `?zero = x"
      unfolding split_paired_Ball
        by (auto simp: pair_plus_def pair_zero_def)

      show "\<forall>x: element (A\<times>B). \<forall>y: element (A\<times>B). \<forall>z: element (A\<times>B). 
          ?plus `(?plus `x `y) `z = ?plus `x `(?plus `y `z)"
      unfolding split_paired_Ball
      by (auto simp: pair_plus_def pair_zero_def)
  qed
qed


lemma [type_instance]:
  "m1 : Plus A \<Longrightarrow> m2 : Plus B \<Longrightarrow> pair_plus A B m1 m2 : Plus (A \<times> B)"
  "m1 : Zero A \<Longrightarrow> m2 : Zero B \<Longrightarrow> pair_zero A B m1 m2 : Zero (A \<times> B)"
  "m1 : Monoid A \<Longrightarrow> m2 : Monoid B \<Longrightarrow> pair_monoid A B m1 m2 : Monoid (A \<times> B)"
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

object Group "A :: set" is
  "Monoid A
  \<bar> \<lparr> (plus @plus) (zero @zero) (inv @inv).
    inv : element (A \<rightarrow> A) \<and>
    (\<forall>x\<in>A. plus `(inv `x) `x = zero) \<and>
    (\<forall>x\<in>A. plus `x `(inv `x) = zero) \<rparr>"

lemma group_is_monoid:  "G : Group A \<Longrightarrow> G : Monoid A"
  unfolding Group_typedef by unfold_types


end
