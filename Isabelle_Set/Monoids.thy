\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
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

definition [typeclass]: "Monoid A \<equiv> Zero A & Add A &
  type (\<lambda>M.
    (\<forall>x : A. add M (zero M) x = x \<and> add M x (zero M) = x) \<and>
    (\<forall>x y z : A. add M (add M x y) z = add M x (add M y z)))"

text \<open>It would be really nice if this worked:\<close>

(* declare [[auto_elaborate]]
lemma MonoidI:
  assumes "M : Zero A" "M : Add A"
  and "\<And>x. x : A \<Longrightarrow> 0 + x = x"
  and "\<And>x. x : A \<Longrightarrow> x + 0 = x"
  and "\<And>x y z. \<lbrakk>x : A; y : A; z : A\<rbrakk> \<Longrightarrow> x + y + z = x + (y + z)"
  shows "M : Monoid A"
  unfolding Monoid_def
  apply unfold_types
  apply auto \<comment>\<open>Doesn't use the assumptions as they weren't elaborated correctly\<close>
  using assms
oops
declare [[auto_elaborate=false]] *)

text \<open>Instead we have to do this for now:\<close>

lemma MonoidI:
  assumes "M : Zero A" "M : Add A"
  and "\<And>x. x : A \<Longrightarrow> add M (zero M) x = x"
  and "\<And>x. x : A \<Longrightarrow> add M x (zero M) = x"
  and "\<And>x y z. \<lbrakk>x : A; y : A; z : A\<rbrakk> \<Longrightarrow>
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
    "\<And>x. M : Monoid A \<Longrightarrow> x : A \<Longrightarrow> add M (zero M) x = x"
  and Monoid_add_zero_eq [simp]:
    "\<And>x. M : Monoid A \<Longrightarrow> x : A \<Longrightarrow> add M x (zero M) = x"
  and Monoid_add_assoc:
    "\<And>x y z. \<lbrakk>M : Monoid A; x : A; y : A; z : A\<rbrakk> \<Longrightarrow>
      add M (add M x y) z = add M x (add M y z)"
  (* TODO: should be provable by type checker *)
  unfolding Monoid_def by (auto 7 0 dest!: Int_typeD1 Int_typeD2 has_typeD)


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
  by (intro Dep_fun_typeI, rule ZeroI) auto

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

(* TODO: quite challenging for automatic type derivation *)
lemma Add_pair_type [type]:
  "Add_pair: (A : Set) \<Rightarrow> (B : Set) \<Rightarrow> Add (Element A) \<Rightarrow> Add (Element B)
    \<Rightarrow> Add (Element (A \<times> B))"
proof (intro Dep_fun_typeI AddI, subst Add_pair_add_eq)
  fix A B AA AB assume h: "AA : Add (Element A)" "AB : Add (Element B)"
  let ?f = "\<lambda>\<langle>a1, b1\<rangle> \<in> A \<times> B. \<lambda>\<langle>a2, b2\<rangle> \<in> A \<times> B. \<langle>add AA a1 a2, add AB b1 b2\<rangle>"
  from h have "?f : Element (A \<times> B) \<rightarrow>c Element (A \<times> B) \<rightarrow>c Element (A \<times> B)"
    by (auto iff: Element_dep_pairs_iff_Dep_Pair
      intro!: lambda_app_type Dep_fun_typeI, discharge_types)
  then show "?f : Element (A \<times> B) \<rightarrow> (Element (A \<times> B) \<rightarrow> Element (A \<times> B))"
    using Dep_Function_covariant_codom by auto
qed

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
  "Monoid_pair : (A : Set) \<Rightarrow> (B : Set) \<Rightarrow> Monoid (Element A) \<Rightarrow>
    Monoid (Element B) \<Rightarrow> Monoid (Element (A \<times> B))"
proof (intro Dep_fun_typeI MonoidI)
  fix A B MA MB assume "MA : Monoid (Element A)" "MB : Monoid (Element B)"
  let ?M = "Monoid_pair A B MA MB"
  show "?M : Zero (Element (A \<times> B))"
    by (rule ZeroI) (auto iff: Element_dep_pairs_iff_Dep_Pair)
  have 1: "\<And>p. p : Element (A \<times> B) \<longleftrightarrow> p : Element A \<times> Element B"
    by unfold_types auto
  have "\<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle> \<in> A \<times> B. \<langle>add MA a1 a2, add MB b1 b2\<rangle>
    : Element (A \<times> B) \<rightarrow>c Element (A \<times> B) \<rightarrow>c Element (A \<times> B)"
    using [[type_derivation_depth=8]]
    apply (rule lambda_app_type)
    apply (rule Dep_fun_contravariant_dom[where ?A="Element A \<times> Element B"])
    apply (rule uncurry_app_type)
    apply (intro Dep_fun_typeI)
    apply (rule lambda_app_type)
    apply (rule Dep_fun_contravariant_dom[where ?A="Element A \<times> Element B"])
    apply (rule uncurry_app_type)
    apply (intro Dep_fun_typeI)
    apply (simp_all only: 1)
    done
  then have "\<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle> \<in> A \<times> B. \<langle>add MA a1 a2, add MB b1 b2\<rangle>
    : Element (A \<times> B) \<rightarrow> Element (A \<times> B) \<rightarrow> Element (A \<times> B)"
    by (auto intro: Dep_Function_if_CDep_Function CDep_Function_covariant_codom)
  show "?M : Add (Element (A \<times> B))"
    (*TODO: this should also work*)
    (* by (rule AddI) simp*)
    by (rule AddI, subst Monoid_pair_add_eq) fact

  fix x assume "x : Element (A \<times> B)"
  then show "add ?M (zero ?M) x = x" and "add ?M x (zero ?M) = x"
    unfolding add_def zero_def by (auto iff: 1)

  fix y z assume "y : Element (A \<times> B)" "z : Element (A \<times> B)"
  then show "add ?M (add ?M x y) z = add ?M x (add ?M y z)"
    unfolding add_def using \<open>x : Element (A \<times> B)\<close> Monoid_add_assoc
oops

lemma [type_instance]:
  "MA : Zero A \<Longrightarrow> MB : Zero B \<Longrightarrow> Zero_pair MA MB : Zero (A \<times> B)"
  by discharge_types

lemma [type_instance]:
  "MA : Add (Element A) \<Longrightarrow> MB : Add (Element B) \<Longrightarrow>
    Add_pair A B MA MB : Add (Element (A \<times> B))"
  by discharge_types

lemma [type_instance]:
  "MA : Monoid (Element A) \<Longrightarrow> MB : Monoid (Element B) \<Longrightarrow>
    Monoid_pair A B MA MB : Monoid (Element (A \<times> B))"
oops


(* subsection \<open>Overloaded syntax\<close>

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

end *)


subsection \<open>Extension to groups\<close>

definition [typeclass]: "Group A \<equiv> Monoid A & Inv A &
  type (\<lambda>G.
    (\<forall>x : A. add G x (inv G x) = zero G) \<and>
    (\<forall>x : A. add G (inv G x) x = zero G))"

lemma GroupI [type_intro]:
  assumes "G : Monoid A" "G : Inv A"
  and "\<And>x. x : A \<Longrightarrow> add G x (inv G x) = zero G"
  and "\<And>x. x : A \<Longrightarrow> add G (inv G x) x = zero G"
  shows "G : Group A"
  unfolding Group_def
  by (intro Int_typeI has_typeI) (auto intro: assms)

lemma Group_Monoid [derive]:  "G : Group A \<Longrightarrow> G : Monoid A"
  unfolding Group_def by (drule Int_typeD1)+

definition [typeclass]: "Comm_Group A \<equiv> Group A &
  type (\<lambda>G. \<forall>a b : A. add G a b = add G b a)"

lemma Comm_GroupI [type_intro]:
  assumes "G : Group A"
  and "\<And>x y. x : A \<Longrightarrow> y : A \<Longrightarrow> add G x y = add G y x"
  shows "G : Comm_Group A"
  unfolding Comm_Group_def
  by (intro Int_typeI has_typeI) (auto intro: assms)

lemma shows Comm_Group_Group [derive]: "G : Comm_Group A \<Longrightarrow> G : Group A"
  unfolding Comm_Group_def by (drule Int_typeD1)

lemma shows Comm_Group_add_comm:
  "\<And>x y. \<lbrakk>G : Comm_Group A; x : A; y : A\<rbrakk> \<Longrightarrow> add G x y = add G y x"
  unfolding Comm_Group_def by (auto dest: Int_typeD2 has_typeD)


subsection \<open>Multiplicative monoids\<close>

text \<open>This is just a copy of the additive monoid structure above and should be
automatically generated in the future, or be put in a unified framework.\<close>

definition [typeclass]: "Mul_Monoid A \<equiv> One A & Mul A &
  type (\<lambda>M.
    (\<forall>x : A. mul M (one M) x = x \<and> mul M x (one M) = x) \<and>
    (\<forall>x y z : A. mul M (mul M x y) z = mul M x (mul M y z)))"

lemma Mul_MonoidI:
  assumes "M : One A" "M : Mul A"
  and "\<And>x. x : A \<Longrightarrow> mul M (one M) x = x"
  and "\<And>x. x : A \<Longrightarrow> mul M x (one M) = x"
  and "\<And>x y z. \<lbrakk>x : A; y : A; z : A\<rbrakk> \<Longrightarrow>
    mul M (mul M x y) z = mul M x (mul M y z)"
  shows "M : Mul_Monoid A"
  unfolding Mul_Monoid_def by (intro Int_typeI has_typeI) (auto intro: assms)

lemma
  shows Mul_Monoid_One [derive]: "M : Mul_Monoid A \<Longrightarrow> M : One A"
  and Mul_Monoid_Mul [derive]: "M : Mul_Monoid A \<Longrightarrow> M : Mul A"
  and Mul_Monoid_one_mul_eq [simp]:
    "\<And>x. M : Mul_Monoid A \<Longrightarrow> x : A \<Longrightarrow> mul M (one M) x = x"
  and Mul_Monoid_mul_one_eq [simp]:
    "\<And>x. M : Mul_Monoid A \<Longrightarrow> x : A \<Longrightarrow> mul M x (one M) = x"
  and Mul_Monoid_mul_assoc:
    "\<And>x y z. \<lbrakk>M : Mul_Monoid A; x : A; y : A; z : A\<rbrakk> \<Longrightarrow>
      mul M (mul M x y) z = mul M x (mul M y z)"
  (* TODO: should be provable by type checker *)
  unfolding Mul_Monoid_def by (auto 7 0 dest!: Int_typeD1 Int_typeD2 has_typeD)


end
