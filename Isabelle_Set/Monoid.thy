section \<open>Monoids\<close>

text \<open>
  An experiment with softly-typed set-theoretic type classes.

  We define monoids as a soft type class and experiment with how it interacts
  with implicit arguments and type inference. Everything is done manually here;
  most of it will be automated away in future work.
\<close>

theory Monoid
imports Structures

begin

text \<open>
  The monoid typeclass is defined using the standard soft type infrastructure.
\<close>

definition [typeclass]: "Monoid A = Zero A \<bar> Add A \<bar>
  type (\<lambda>M.
    (\<forall>x\<in> A.
      add M (zero M) x = x \<and>
      add M x (zero M) = x) \<and>
    (\<forall>x y z \<in> A.
      add M (add M x y) z = add M x (add M y z))
  )"

text \<open>It would be really nice if this worked:\<close>

declare [[auto_elaborate]]
lemma MonoidI:
  assumes "M : Zero A"
          "M : Add A"
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

lemma MonoidI [typeI]:
  assumes "M : Zero A"
          "M : Add A"
          "\<And>x. x \<in> A \<Longrightarrow> add M (zero M) x = x"
          "\<And>x. x \<in> A \<Longrightarrow> add M x (zero M) = x"
          "\<And>x y z. \<lbrakk>x \<in> A; y \<in> A; z \<in> A\<rbrakk>
            \<Longrightarrow> add M (add M x y) z = add M x (add M y z)"
  shows "M : Monoid A"
  unfolding Monoid_def by unfold_types (auto intro: assms)

text \<open>
  The above theorem as well as the next ones should also be automatically
  generated.
\<close>

lemma
  shows
    Monoid_Zero [derive]: "M : Monoid A \<Longrightarrow> M : Zero A" and
    Monoid_Add [derive]: "M : Monoid A \<Longrightarrow> M : Add A"
  and
    zero_add: "\<And>x. M : Monoid A \<Longrightarrow> x \<in> A \<Longrightarrow> add M (zero M) x = x" and
    add_zero: "\<And>x. M : Monoid A \<Longrightarrow> x \<in> A \<Longrightarrow> add M x (zero M) = x" and
    add_assoc: "\<And>x y z. \<lbrakk>M : Monoid A; x \<in> A; y \<in> A; z \<in> A\<rbrakk>
                    \<Longrightarrow> add M (add M x y) z = add M x (add M y z)"
  unfolding Monoid_def
  subgoal by (drule Int_typeE1, drule Int_typeE1)
  subgoal by (drule Int_typeE1, drule Int_typeE2)
  subgoal by (drule Int_typeE2, drule has_type_typeE) auto
  subgoal by (drule Int_typeE2, drule has_type_typeE) auto
  subgoal by (drule Int_typeE2, drule has_type_typeE) auto
  done


subsection \<open>Direct sum\<close>

text \<open>
  In this section we develop the structure constructor for direct sums of
  monoids, by defining it as the (disjoint) structure union of the zero and add
  pair structures.

  We emulate automation that needs to be implemented in future work.
\<close>

definition "Zero_Pair Z1 Z2 = object {\<langle>@zero, \<langle>zero Z1, zero Z2\<rangle>\<rangle>}"

(*These should be automatically generated*)
lemma Zero_Pair_fields [simp]: "object_fields (Zero_Pair Z1 Z2) = {@zero}"
  unfolding Zero_Pair_def by auto

lemma Zero_Pair_zero [simp]: "(Zero_Pair Z1 Z2) @@ zero = \<langle>zero Z1, zero Z2\<rangle>"
  unfolding Zero_Pair_def by simp

definition "Add_Pair A B P1 P2 = object {
  \<langle>@add, \<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle>\<in> A \<times> B. \<langle>add P1 a1 a2, add P2 b1 b2\<rangle>\<rangle>}"

(*Should be automatically generated*)
lemma Add_Pair_fields [simp]: "object_fields (Add_Pair A B P1 P2) = {@add}"
  unfolding Add_Pair_def by auto

lemma Add_Pair_add [simp]:
  "(Add_Pair A B P1 P2) @@ add =
    \<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle>\<in> A \<times> B. \<langle>add P1 a1 a2, add P2 b1 b2\<rangle>"
  unfolding Add_Pair_def by simp

text \<open>
  Monoid direct sum is the composition of the respective zero and pair instances.
  Eventually we'd want a composition keyword [+] of some kind, so e.g.
    \<open>Monoid_Sum A B M1 M2 = Zero_Pair M1 M2 [+] Add_Pair A B M1 M2\<close>
  should generate the following definition, which we write manually for now.
\<close>

definition "Monoid_Sum A B M1 M2 = object {
  \<langle>@zero, \<langle>zero M1, zero M2\<rangle>\<rangle>,
  \<langle>@add, \<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle>\<in> A \<times> B. \<langle>add M1 a1 a2, add M2 b1 b2\<rangle>\<rangle>}"

lemma Monoid_Sum_fields [simp]:
  "object_fields (Monoid_Sum A B M1 M2) = {@zero, @add}"
  unfolding Monoid_Sum_def by simp

lemma [simp]:
  shows
    Monoid_Sum_zero:
      "(Monoid_Sum A B M1 M2) @@ zero = \<langle>zero M1, zero M2\<rangle>"
  and
    Monoid_Sum_add:
      "(Monoid_Sum A B M1 M2) @@ add =
        \<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle>\<in> A \<times> B. \<langle>add M1 a1 a2, add M2 b1 b2\<rangle>"
  unfolding Monoid_Sum_def by auto

text \<open>
  The following proofs illustrate that reasoning with types is still very
  pedestrian and needs better automated support.
\<close>

lemma Zero_Pair_type [type]:
  "Zero_Pair : Zero A \<Rightarrow> Zero B \<Rightarrow> Zero (A \<times> B)"
  unfolding Zero_Pair_def
  by unfold_types (auto simp: zero_def)

lemma Add_Pair_type [type]:
  "Add_Pair : (A : set) \<Rightarrow> (B : set) \<Rightarrow> Add A \<Rightarrow> Add B \<Rightarrow> Add (A \<times> B)"
  unfolding Add_Pair_def add_def
  by unfold_types fastforce

lemma Monoid_Sum_type [type]:
  "Monoid_Sum : (A : set) \<Rightarrow> (B : set) \<Rightarrow> Monoid A \<Rightarrow> Monoid B \<Rightarrow> Monoid (A \<times> B)"
proof (intro typeI)
  fix A B M1 M2 assume assms1: "M1 : Monoid A" "M2 : Monoid B"

  show "Monoid_Sum A B M1 M2 : Zero (A \<times> B)"
    using assms1 by (intro Zero_typeI) (auto dest!: Monoid_Zero)

  show "Monoid_Sum A B M1 M2 : Add (A \<times> B)"
    by (intro Add_typeI, simp add: Monoid_Sum_def) (unfold_types, force)

  fix x assume assmx: "x \<in> A \<times> B"

  show "add (Monoid_Sum A B M1 M2) (zero (Monoid_Sum A B M1 M2)) x = x"
    unfolding add_def zero_def using assms1 assmx zero_add by auto

  show "add (Monoid_Sum A B M1 M2) x (zero (Monoid_Sum A B M1 M2)) = x"
    unfolding add_def zero_def using assms1 assmx add_zero by auto

  fix y z assume assmsyz: "y \<in> A \<times> B" "z \<in> A \<times> B"

  show "add (Monoid_Sum A B M1 M2) (add (Monoid_Sum A B M1 M2) x y) z =
        add (Monoid_Sum A B M1 M2) x (add (Monoid_Sum A B M1 M2) y z)"
    unfolding add_def using assms1 assmx assmsyz add_assoc by force
qed

lemma [type_instance]:
  "M1 : Add A \<Longrightarrow> M2 : Add B \<Longrightarrow> Add_Pair A B M1 M2 : Add (A \<times> B)"
  "M1 : Zero A \<Longrightarrow> M2 : Zero B \<Longrightarrow> Zero_Pair M1 M2 : Zero (A \<times> B)"
  "M1 : Monoid A \<Longrightarrow> M2 : Monoid B \<Longrightarrow> Monoid_Sum A B M1 M2 : Monoid (A \<times> B)"
  by auto


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

definition [typeclass]: "Group A = Monoid A \<bar>
  type (\<lambda>G.
    G @@ inv \<in> A \<rightarrow> A \<and>
    (\<forall>x\<in> A. add G x (G@@inv `x) = zero G) \<and>
    (\<forall>x\<in> A. add G (G@@inv `x) x = zero G)
  )"

lemma Group_Monoid [derive]:  "G : Group A \<Longrightarrow> G : Monoid A"
  unfolding Group_def by (fact Int_typeE1)

definition [typeclass]: "Comm_Group A \<equiv> Group A \<bar> type (\<lambda>P. \<forall> a b \<in> A. add P a b = add P b a)"

subsection \<open>Multiplicative Structures\<close>

text \<open>This is just a copy of the additive structures above and should be automatically generated
in the future or be put in a unified framework.\<close>

definition [typeclass]: "Mul_Monoid A = One A \<bar> Mul A \<bar>
  type (\<lambda>M.
    (\<forall>x\<in> A.
      mul M (one M) x = x \<and>
      mul M x (one M) = x) \<and>
    (\<forall>x y z \<in> A.
      mul M (mul M x y) z = mul M x (mul M y z))
  )"

lemma Mul_MonoidI [typeI]:
  assumes "M : One A"
          "M : Mul A"
          "\<And>x. x \<in> A \<Longrightarrow> mul M (one M) x = x"
          "\<And>x. x \<in> A \<Longrightarrow> mul M x (one M) = x"
          "\<And>x y z. \<lbrakk>x \<in> A; y \<in> A; z \<in> A\<rbrakk>
            \<Longrightarrow> mul M (mul M x y) z = mul M x (mul M y z)"
  shows "M : Mul_Monoid A"
  unfolding Mul_Monoid_def by unfold_types (auto intro: assms)

lemma
  shows
    Mul_Monoid_One [derive]: "M : Mul_Monoid A \<Longrightarrow> M : One A" and
    Mul_Monoid_Mul [derive]: "M : Mul_Monoid A \<Longrightarrow> M : Mul A"
  and
    one_mul: "\<And>x. M : Mul_Monoid A \<Longrightarrow> x \<in> A \<Longrightarrow> mul M (one M) x = x" and
    mul_one: "\<And>x. M : Mul_Monoid A \<Longrightarrow> x \<in> A \<Longrightarrow> mul M x (one M) = x" and
    mul_assoc: "\<And>x y z. \<lbrakk>M : Mul_Monoid A; x \<in> A; y \<in> A; z \<in> A\<rbrakk>
                    \<Longrightarrow> mul M (mul M x y) z = mul M x (mul M y z)"
  unfolding Mul_Monoid_def
  subgoal by (drule Int_typeE1, drule Int_typeE1)
  subgoal by (drule Int_typeE1, drule Int_typeE2)
  subgoal by (drule Int_typeE2, drule has_type_typeE) auto
  subgoal by (drule Int_typeE2, drule has_type_typeE) auto
  subgoal by (drule Int_typeE2, drule has_type_typeE) auto
  done

end
