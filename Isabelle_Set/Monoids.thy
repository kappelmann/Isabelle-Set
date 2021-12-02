section \<open>Monoids\<close>
theory Monoids
imports Structures

begin
text \<open>An experiment with softly-typed, set-theoretic type classes.

We define monoids as a soft type class and experiment with how it interacts
with implicit arguments and type inference. Everything is done manually here;
most of it will be automated away in future work.\<close>

text \<open>The monoid typeclass is defined using the standard soft type
infrastructure.\<close>

definition [typeclass]: "Monoid A \<equiv> Zero A \<bar> Add A \<bar>
  type (\<lambda>M.
    (\<forall>x \<in> A. add M (zero M) x = x \<and> add M x (zero M) = x) \<and>
    (\<forall>x y z \<in> A. add M (add M x y) z = add M x (add M y z)))"

text \<open>It would be really nice if this worked:\<close>

declare [[auto_elaborate]]
lemma MonoidI:
  assumes "M : Zero A" "M : Add A"
  and "\<And>x. x \<in> A \<Longrightarrow> 0 + x = x"
  and "\<And>x. x \<in> A \<Longrightarrow> x + 0 = x"
  and "\<And>x y z. \<lbrakk>x \<in> A; y \<in> A; z \<in> A\<rbrakk> \<Longrightarrow> x + y + z = x + (y + z)"
  shows "M : Monoid A"
  unfolding Monoid_def
  apply unfold_types
  apply auto \<comment>\<open>Doesn't use the assumptions as they weren't elaborated correctly\<close>
  using assms
oops
declare [[auto_elaborate=false]]

text \<open>Instead we have to do this for now:\<close>

lemma MonoidI:
  assumes "M : Zero A" "M : Add A"
  and "\<And>x. x \<in> A \<Longrightarrow> add M (zero M) x = x"
  and "\<And>x. x \<in> A \<Longrightarrow> add M x (zero M) = x"
  and "\<And>x y z. \<lbrakk>x \<in> A; y \<in> A; z \<in> A\<rbrakk> \<Longrightarrow>
    add M (add M x y) z = add M x (add M y z)"
  shows "M : Monoid A"
  unfolding Monoid_def
  by (intro Int_typeI has_typeI) (auto intro: assms)

text \<open>The above theorem as well as the next ones should also be automatically
generated.\<close>

lemma
  shows Monoid_Zero [derive]: "M : Monoid A \<Longrightarrow> M : Zero A"
  and Monoid_Add [derive]: "M : Monoid A \<Longrightarrow> M : Add A"
  and Monoid_zero_add_eq [simp]:
    "\<And>x. M : Monoid A \<Longrightarrow> x \<in> A \<Longrightarrow> add M (zero M) x = x"
  and Monoid_add_zero_eq [simp]:
    "\<And>x. M : Monoid A \<Longrightarrow> x \<in> A \<Longrightarrow> add M x (zero M) = x"
  and Monoid_add_assoc:
    "\<And>x y z. \<lbrakk>M : Monoid A; x \<in> A; y \<in> A; z \<in> A\<rbrakk> \<Longrightarrow>
      add M (add M x y) z = add M x (add M y z)"
  (* TODO: should be provable by type checker *)
  unfolding Monoid_def by (auto dest!: Int_typeD1 Int_typeD2 has_typeD)


subsection \<open>Direct sum\<close>

text \<open>We develop the construction of direct sums of monoids by defining it as
the (disjoint) union of the zero and add structures.

We emulate automation that needs to be implemented in future work.\<close>

definition "Zero_pair Z1 Z2 \<equiv> object {\<langle>@zero, \<langle>zero Z1, zero Z2\<rangle>\<rangle>}"

(*TODO: These should be automatically generated*)
lemma Zero_pair_fields_eq [simp]: "object_fields (Zero_pair Z1 Z2) = {@zero}"
  unfolding Zero_pair_def by simp

lemma Zero_pair_zero_eq [simp]: "(Zero_pair Z1 Z2) @@ zero = \<langle>zero Z1, zero Z2\<rangle>"
  unfolding Zero_pair_def by simp

lemma Zero_pair_type [type]: "Zero_pair: Zero A \<Rightarrow> Zero B \<Rightarrow> Zero (A \<times> B)"
  by (intro Dep_fun_typeI, rule ZeroI) simp

definition "Add_pair A B AA AB \<equiv> object {
    \<langle>@add, \<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle> \<in> A \<times> B. \<langle>add AA a1 a2, add AB b1 b2\<rangle>\<rangle>
  }"

(*TODO: These should be automatically generated*)
lemma Add_pair_fields_eq [simp]: "object_fields (Add_pair A B AA AB) = {@add}"
  unfolding Add_pair_def by simp

lemma Add_pair_add_eq [simp]:
  "(Add_pair A B AA AB) @@ add =
    \<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle> \<in> A \<times> B. \<langle>add AA a1 a2, add AB b1 b2\<rangle>"
  unfolding Add_pair_def by simp

lemma Add_pair_type [type]:
  "Add_pair: (A : Set) \<Rightarrow> (B : Set) \<Rightarrow> Add A \<Rightarrow> Add B \<Rightarrow> Add (A \<times> B)"
  (*these do not work for some reason*)
  (* by auto *)
  (* by (intro Dep_fun_typeI, rule AddI) simp *)
  by (intro Dep_fun_typeI AddI, subst Add_pair_add_eq) discharge_types

text \<open>TODO: In the future, there should be a command for object
composition/extension.\<close>

definition "Monoid_pair A B MA MB \<equiv> object {
    \<langle>@zero, \<langle>zero MA, zero MB\<rangle>\<rangle>,
    \<langle>@add, \<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle> \<in> A \<times> B. \<langle>add MA a1 a2, add MB b1 b2\<rangle>\<rangle>
  }"

lemma Monoid_pair_fields_eq [simp]:
  "object_fields (Monoid_pair A B MA MB) = {@zero, @add}"
  unfolding Monoid_pair_def by simp

lemma [simp]:
  shows Monoid_pair_zero_eq:
    "(Monoid_pair A B MA MB) @@ zero = \<langle>zero MA, zero MB\<rangle>"
  and Monoid_pair_add_eq:
    "(Monoid_pair A B MA MB) @@ add =
      \<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle> \<in> A \<times> B. \<langle>add MA a1 a2, add MB b1 b2\<rangle>"
  unfolding Monoid_pair_def by auto

text \<open>The following proofs illustrate that reasoning with types is still very
pedestrian and needs better automated support.\<close>

lemma Monoid_pair_type [type]:
  "Monoid_pair : (A : Set) \<Rightarrow> (B : Set) \<Rightarrow> Monoid A \<Rightarrow> Monoid B \<Rightarrow> Monoid (A \<times> B)"
proof (intro Dep_fun_typeI MonoidI)
  fix A B MA MB assume "MA : Monoid A" "MB : Monoid B"
  let ?M = "Monoid_pair A B MA MB"
  show "?M : Zero (A \<times> B)"
    (*TODO: should not need a limit increase*)
    using [[type_derivation_depth=3]]
    by (rule ZeroI) simp
  show "?M : Add (A \<times> B)"
    (*TODO: should not need a limit increase*)
    using [[type_derivation_depth=3]]
    (*TODO: this should also work*)
    (* by (rule AddI) simp*)
    by (rule AddI, subst Monoid_pair_add_eq) discharge_types

  fix x assume "x \<in> A \<times> B"
  then show "add ?M (zero ?M) x = x" and "add ?M x (zero ?M) = x"
    unfolding add_def zero_def by auto

  fix y z assume "y \<in> A \<times> B" "z \<in> A \<times> B"
  then show "add ?M (add ?M x y) z = add ?M x (add ?M y z)"
    unfolding add_def using \<open>x \<in> A \<times> B\<close> Monoid_add_assoc by auto
qed

lemma [type_instance]:
  "MA : Add A \<Longrightarrow> MB : Add B \<Longrightarrow> Add_pair A B MA MB : Add (A \<times> B)"
  "MA : Zero A \<Longrightarrow> MB : Zero B \<Longrightarrow> Zero_pair MA MB : Zero (A \<times> B)"
  "MA : Monoid A \<Longrightarrow> MB : Monoid B \<Longrightarrow> Monoid_pair A B MA MB : Monoid (A \<times> B)"
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

definition [typeclass]: "Group A \<equiv> Monoid A \<bar> Inv A \<bar>
  type (\<lambda>G.
    (\<forall>x \<in> A. add G x (inv G x) = zero G) \<and>
    (\<forall>x \<in> A. add G (inv G x) x = zero G))"

lemma GroupI [type_intro]:
  assumes "G : Monoid A" "G : Inv A"
  and "\<And>x. x \<in> A \<Longrightarrow> add G x (inv G x) = zero G"
  and "\<And>x. x \<in> A \<Longrightarrow> add G (inv G x) x = zero G"
  shows "G : Group A"
  unfolding Group_def
  by (intro Int_typeI has_typeI) (auto intro: assms)

lemma Group_Monoid [derive]:  "G : Group A \<Longrightarrow> G : Monoid A"
  unfolding Group_def by (drule Int_typeD1)+

definition [typeclass]: "Comm_Group A \<equiv> Group A \<bar>
  type (\<lambda>G. \<forall>a b \<in> A. add G a b = add G b a)"

lemma Comm_GroupI [type_intro]:
  assumes "G : Group A"
  and "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> add G x y = add G y x"
  shows "G : Comm_Group A"
  unfolding Comm_Group_def
  by (intro Int_typeI has_typeI) (auto intro: assms)

lemma shows Comm_Group_Group [derive]: "G : Comm_Group A \<Longrightarrow> G : Group A"
  unfolding Comm_Group_def by (drule Int_typeD1)

lemma shows Comm_Group_add_comm:
  "\<And>x y. \<lbrakk>G : Comm_Group A; x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> add G x y = add G y x"
  unfolding Comm_Group_def by (auto dest: Int_typeD2 has_typeD)


subsection \<open>Multiplicative monoids\<close>

text \<open>This is just a copy of the additive monoid structure above and should be
automatically generated in the future, or be put in a unified framework.\<close>

definition [typeclass]: "Mul_Monoid A \<equiv> One A \<bar> Mul A \<bar>
  type (\<lambda>M.
    (\<forall>x \<in> A. mul M (one M) x = x \<and> mul M x (one M) = x) \<and>
    (\<forall>x y z \<in> A. mul M (mul M x y) z = mul M x (mul M y z)))"

lemma Mul_MonoidI:
  assumes "M : One A" "M : Mul A"
  and "\<And>x. x \<in> A \<Longrightarrow> mul M (one M) x = x"
  and "\<And>x. x \<in> A \<Longrightarrow> mul M x (one M) = x"
  and "\<And>x y z. \<lbrakk>x \<in> A; y \<in> A; z \<in> A\<rbrakk> \<Longrightarrow>
    mul M (mul M x y) z = mul M x (mul M y z)"
  shows "M : Mul_Monoid A"
  unfolding Mul_Monoid_def by (intro Int_typeI has_typeI) (auto intro: assms)

lemma
  shows Mul_Monoid_One [derive]: "M : Mul_Monoid A \<Longrightarrow> M : One A"
  and Mul_Monoid_Mul [derive]: "M : Mul_Monoid A \<Longrightarrow> M : Mul A"
  and Mul_Monoid_one_mul_eq [simp]:
    "\<And>x. M : Mul_Monoid A \<Longrightarrow> x \<in> A \<Longrightarrow> mul M (one M) x = x"
  and Mul_Monoid_mul_one_eq [simp]:
    "\<And>x. M : Mul_Monoid A \<Longrightarrow> x \<in> A \<Longrightarrow> mul M x (one M) = x"
  and Mul_Monoid_mul_assoc:
    "\<And>x y z. \<lbrakk>M : Mul_Monoid A; x \<in> A; y \<in> A; z \<in> A\<rbrakk> \<Longrightarrow>
      mul M (mul M x y) z = mul M x (mul M y z)"
  (* TODO: should be provable by type checker *)
  unfolding Mul_Monoid_def by (auto dest!: Int_typeD1 Int_typeD2 has_typeD)


end
