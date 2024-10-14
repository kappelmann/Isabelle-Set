\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Monoids\<close>
theory TSMonoids
  imports
    HOTG.HOTG_Functions_Lambda
    TSClean_Functions
    TSPairs
    TSStructures
begin

unbundle no HOL_ascii_syntax

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
  assumes "M \<Ztypecolon> Zero A" "M \<Ztypecolon> Add A"
  and "\<And>x. x \<Ztypecolon> A \<Longrightarrow> 0 + x = x"
  and "\<And>x. x \<Ztypecolon> A \<Longrightarrow> x + 0 = x"
  and "\<And>x y z. \<lbrakk>x \<Ztypecolon> A; y \<Ztypecolon> A; z \<Ztypecolon> A\<rbrakk> \<Longrightarrow> x + y + z = x + (y + z)"
  shows "M \<Ztypecolon> Monoid A"
  unfolding Monoid_def
  apply unfold_types
  apply auto \<comment>\<open>Doesn't use the assumptions as they weren't elaborated correctly\<close>
  using assms
oops
declare [[auto_elaborate=false]] *)

text \<open>Instead we have to do this for now:\<close>

lemma MonoidI:
  assumes "M \<Ztypecolon> Zero A" "M \<Ztypecolon> Add A"
  and "\<And>x. x \<Ztypecolon> A \<Longrightarrow> add M (zero M) x = x"
  and "\<And>x. x \<Ztypecolon> A \<Longrightarrow> add M x (zero M) = x"
  and "\<And>x y z. \<lbrakk>x \<Ztypecolon> A; y \<Ztypecolon> A; z \<Ztypecolon> A\<rbrakk> \<Longrightarrow>
    add M (add M x y) z = add M x (add M y z)"
  shows "M \<Ztypecolon> Monoid A"
  unfolding Monoid_def
  by (intro InterI type_of_typeI) (auto intro: assms)

text \<open>The above theorem as well as the next ones should also be automatically
generated.\<close>

lemma
  shows Monoid_Zero [derive]: "M \<Ztypecolon> Monoid A \<Longrightarrow> M \<Ztypecolon> Zero A"
  and Monoid_Add [derive]: "M \<Ztypecolon> Monoid A \<Longrightarrow> M \<Ztypecolon> Add A"
  and Monoid_zero_add_eq [simp]:
    "\<And>x. M \<Ztypecolon> Monoid A \<Longrightarrow> x \<Ztypecolon> A \<Longrightarrow> add M (zero M) x = x"
  and Monoid_add_zero_eq [simp]:
    "\<And>x. M \<Ztypecolon> Monoid A \<Longrightarrow> x \<Ztypecolon> A \<Longrightarrow> add M x (zero M) = x"
  and Monoid_add_assoc:
    "\<And>x y z. \<lbrakk>M \<Ztypecolon> Monoid A; x \<Ztypecolon> A; y \<Ztypecolon> A; z \<Ztypecolon> A\<rbrakk> \<Longrightarrow>
      add M (add M x y) z = add M x (add M y z)"
  (* TODO: should be provable by type checker *)
  unfolding Monoid_def by (auto 7 0 dest!: InterD1 InterD2 simp: meaning_of_type)+


subsection \<open>Direct sum\<close>

text \<open>We develop the construction of direct sums of monoids by defining it as
the (disjoint) union of the zero and add structures.

We emulate automation that needs to be implemented in future work.\<close>

definition "Zero_pair Z1 Z2 \<equiv> object {\<langle>$zero, \<langle>zero Z1, zero Z2\<rangle>\<rangle>}"

(*TODO: These should be automatically generated*)
lemma Zero_pair_fields_eq [simp]: "object_fields (Zero_pair Z1 Z2) = {$zero}"
  unfolding Zero_pair_def by simp

lemma Zero_pair_zero_eq [simp]: "(Zero_pair Z1 Z2)@$zero = \<langle>zero Z1, zero Z2\<rangle>"
  unfolding Zero_pair_def by simp

lemma Zero_pair_type [type]: "Zero_pair \<Ztypecolon> Zero A \<Rightarrow> Zero B \<Rightarrow> Zero (A \<times> B)"
  supply [[type_derivation_depth=4]]
  by (intro Dep_funI, rule ZeroI) auto

definition "Add_pair A B AA AB \<equiv> object {
    \<langle>$add, \<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle> : A \<times> B. \<langle>add AA a1 a2, add AB b1 b2\<rangle>\<rangle>
  }"

(*TODO: These should be automatically generated*)
lemma Add_pair_fields_eq [simp]: "object_fields (Add_pair A B AA AB) = {$add}"
  unfolding Add_pair_def by simp

lemma Add_pair_add_eq [simp]:
  "(Add_pair A B AA AB)@$add = \<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle> : A \<times> B. \<langle>add AA a1 a2, add AB b1 b2\<rangle>"
  unfolding Add_pair_def by simp

(* TODO: quite challenging for automatic type derivation *)
lemma Add_pair_type [type]:
  "Add_pair \<Ztypecolon> (A : Set) \<Rightarrow> (B : Set) \<Rightarrow> Add (Element A) \<Rightarrow> Add (Element B) \<Rightarrow> Add (Element A \<times> Element B)"
proof (intro Dep_funI AddI, subst Add_pair_add_eq)
  fix A B AA AB assume h: "AA \<Ztypecolon> Add (Element A)" "AB \<Ztypecolon> Add (Element B)"
  let ?f = "(\<lambda>\<langle>a1, b1\<rangle> : A \<times> B. \<lambda>\<langle>a2, b2\<rangle> : A \<times> B. \<langle>add AA a1 a2, add AB b1 b2\<rangle>) :: set"
  from h have "?f \<Ztypecolon> Element A \<times> Element B \<rightarrow>\<^sub>c Element A \<times> Element B \<rightarrow>\<^sub>c Element A \<times> Element B"
    sorry
  then show "?f \<Ztypecolon> Element A \<times> Element B \<rightarrow> Element A \<times> Element B \<rightarrow> Element A \<times> Element B"
    sorry
qed

text \<open>TODO: In the future, there should be a command for object
composition/extension.\<close>

definition "Monoid_pair A B MA MB \<equiv> object {
    \<langle>$zero, \<langle>zero MA, zero MB\<rangle>\<rangle>,
    \<langle>$add, \<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle> : A \<times> B. \<langle>add MA a1 a2, add MB b1 b2\<rangle>\<rangle>
  }"

lemma Monoid_pair_fields_eq [simp]: "object_fields (Monoid_pair A B MA MB) = {$zero, $add}"
  unfolding Monoid_pair_def by simp

lemma [simp]:
  shows Monoid_pair_zero_eq: "(Monoid_pair A B MA MB)@$zero = \<langle>zero MA, zero MB\<rangle>"
  and Monoid_pair_add_eq: "(Monoid_pair A B MA MB)@$add =
    \<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle> : A \<times> B. \<langle>add MA a1 a2, add MB b1 b2\<rangle>"
  unfolding Monoid_pair_def by auto

text \<open>The following proofs illustrate that reasoning with types is still very
pedestrian and needs better automated support.\<close>

lemma Monoid_pair_type [type]:
  "Monoid_pair \<Ztypecolon> (A : Set) \<Rightarrow> (B : Set) \<Rightarrow> Monoid (Element A) \<Rightarrow>
    Monoid (Element B) \<Rightarrow> Monoid (Element A \<times> Element B)"
proof (intro Dep_funI MonoidI)
  fix A B MA MB assume "MA \<Ztypecolon> Monoid (Element A)" "MB \<Ztypecolon> Monoid (Element B)"
  let ?M = "Monoid_pair A B MA MB"
  show "?M \<Ztypecolon> Zero (Element A \<times> Element B)"
    supply [[type_derivation_depth=4]] by (rule ZeroI) auto
  have "((\<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle> : A \<times> B. \<langle>add MA a1 a2, add MB b1 b2\<rangle>) :: set)
    \<Ztypecolon> Element A \<times> Element B \<rightarrow>\<^sub>c Element A \<times> Element B \<rightarrow>\<^sub>c Element A \<times> Element B"
    sorry
    (* supply [[type_derivation_depth=8]]
    apply (rule lambda_app_type)
    apply (rule Dep_fun_contravariant_dom[where ?A="Element A \<times> Element B"])
    apply (rule uncurry_app_type)
    apply (intro Dep_funI)
    apply (rule lambda_app_type)
    apply (rule Dep_fun_contravariant_dom[where ?A="Element A \<times> Element B"])
    apply (rule uncurry_app_type)
    apply (intro Dep_funI)
    apply (simp_all only: 1)
    done *)
  then have "((\<lambda>\<langle>a1, b1\<rangle> \<langle>a2, b2\<rangle> : A \<times> B. \<langle>add MA a1 a2, add MB b1 b2\<rangle>) :: set)
    \<Ztypecolon> Element A \<times> Element B \<rightarrow> Element A \<times> Element B \<rightarrow> Element A \<times> Element B"
    sorry
  show "?M \<Ztypecolon> Add (Element A \<times> Element B)"
    (*TODO: this should also work*)
    (* by (rule AddI) simp*)
    by (rule AddI, subst Monoid_pair_add_eq) fact

  fix x assume "x \<Ztypecolon> Element A \<times> Element B"
  then show "add ?M (zero ?M) x = x" and "add ?M x (zero ?M) = x"
    (* unfolding add_def zero_def by simp *)
    sorry

  fix y z assume "y \<Ztypecolon> Element A \<times> Element B" "z \<Ztypecolon> Element A \<times> Element B"
  then show "add ?M (add ?M x y) z = add ?M x (add ?M y z)"
    unfolding add_def using \<open>x \<Ztypecolon> Element A \<times> Element B\<close> Monoid_add_assoc
oops

lemma [type_instance]:
  "MA \<Ztypecolon> Zero A \<Longrightarrow> MB \<Ztypecolon> Zero B \<Longrightarrow> Zero_pair MA MB \<Ztypecolon> Zero (A \<times> B)"
  by discharge_types

lemma [type_instance]:
  "MA \<Ztypecolon> Add (Element A) \<Longrightarrow> MB \<Ztypecolon> Add (Element B) \<Longrightarrow>
    Add_pair A B MA MB \<Ztypecolon> Add (Element A \<times> Element B)"
  by discharge_types

lemma [type_instance]:
  "MA \<Ztypecolon> Monoid (Element A) \<Longrightarrow> MB \<Ztypecolon> Monoid (Element B) \<Longrightarrow>
    Monoid_pair A B MA MB \<Ztypecolon> Monoid (Element A \<times> Element B)"
oops


(* subsection \<open>Overloaded syntax\<close>

context
  notes [[auto_elaborate, trace_soft_types]]
begin

lemma "x + 0 = x"
  printers
  oops

lemma "\<langle>x, y\<rangle> + 0 = \<langle>x, y\<rangle>"
  printers
  oops

lemma "x + (y + z) = x + y + z"
  printers
  oops

lemma "x + y = z + w \<and> u + v = 0"
  printers
  oops

end *)


subsection \<open>Extension to groups\<close>

definition [typeclass]: "Group A \<equiv> Monoid A & Inv A &
  type (\<lambda>G.
    (\<forall>x : A. add G x (inv G x) = zero G) \<and>
    (\<forall>x : A. add G (inv G x) x = zero G))"

lemma GroupI [type_intro]:
  assumes "G \<Ztypecolon> Monoid A" "G \<Ztypecolon> Inv A"
  and "\<And>x. x \<Ztypecolon> A \<Longrightarrow> add G x (inv G x) = zero G"
  and "\<And>x. x \<Ztypecolon> A \<Longrightarrow> add G (inv G x) x = zero G"
  shows "G \<Ztypecolon> Group A"
  unfolding Group_def
  by (intro InterI type_of_typeI) (auto intro: assms)

lemma Group_Monoid [derive]:  "G \<Ztypecolon> Group A \<Longrightarrow> G \<Ztypecolon> Monoid A"
  unfolding Group_def by (drule InterD1)+

definition [typeclass]: "Comm_Group A \<equiv> Group A & type (\<lambda>G. \<forall>a b : A. add G a b = add G b a)"

lemma Comm_GroupI [type_intro]:
  assumes "G \<Ztypecolon> Group A"
  and "\<And>x y. x \<Ztypecolon> A \<Longrightarrow> y \<Ztypecolon> A \<Longrightarrow> add G x y = add G y x"
  shows "G \<Ztypecolon> Comm_Group A"
  unfolding Comm_Group_def
  by (intro InterI type_of_typeI) (auto intro: assms)

lemma shows Comm_Group_Group [derive]: "G \<Ztypecolon> Comm_Group A \<Longrightarrow> G \<Ztypecolon> Group A"
  unfolding Comm_Group_def by (drule InterD1)

lemma shows Comm_Group_add_comm:
  "\<And>x y. \<lbrakk>G \<Ztypecolon> Comm_Group A; x \<Ztypecolon> A; y \<Ztypecolon> A\<rbrakk> \<Longrightarrow> add G x y = add G y x"
  by unfold_types auto

subsection \<open>Multiplicative monoids\<close>

text \<open>This is just a copy of the additive monoid structure above and should be
automatically generated in the future, or be put in a unified framework.\<close>

definition [typeclass]: "Mul_Monoid A \<equiv> One A & Mul A &
  type (\<lambda>M.
    (\<forall>x : A. mul M (one M) x = x \<and> mul M x (one M) = x) \<and>
    (\<forall>x y z : A. mul M (mul M x y) z = mul M x (mul M y z)))"

lemma Mul_MonoidI:
  assumes "M \<Ztypecolon> One A" "M \<Ztypecolon> Mul A"
  and "\<And>x. x \<Ztypecolon> A \<Longrightarrow> mul M (one M) x = x"
  and "\<And>x. x \<Ztypecolon> A \<Longrightarrow> mul M x (one M) = x"
  and "\<And>x y z. \<lbrakk>x \<Ztypecolon> A; y \<Ztypecolon> A; z \<Ztypecolon> A\<rbrakk> \<Longrightarrow>
    mul M (mul M x y) z = mul M x (mul M y z)"
  shows "M \<Ztypecolon> Mul_Monoid A"
  unfolding Mul_Monoid_def by (intro InterI type_of_typeI) (auto intro: assms)

lemma
  shows Mul_Monoid_One [derive]: "M \<Ztypecolon> Mul_Monoid A \<Longrightarrow> M \<Ztypecolon> One A"
  and Mul_Monoid_Mul [derive]: "M \<Ztypecolon> Mul_Monoid A \<Longrightarrow> M \<Ztypecolon> Mul A"
  and Mul_Monoid_one_mul_eq [simp]:
    "\<And>x. M \<Ztypecolon> Mul_Monoid A \<Longrightarrow> x \<Ztypecolon> A \<Longrightarrow> mul M (one M) x = x"
  and Mul_Monoid_mul_one_eq [simp]:
    "\<And>x. M \<Ztypecolon> Mul_Monoid A \<Longrightarrow> x \<Ztypecolon> A \<Longrightarrow> mul M x (one M) = x"
  and Mul_Monoid_mul_assoc:
    "\<And>x y z. \<lbrakk>M \<Ztypecolon> Mul_Monoid A; x \<Ztypecolon> A; y \<Ztypecolon> A; z \<Ztypecolon> A\<rbrakk> \<Longrightarrow>
      mul M (mul M x y) z = mul M x (mul M y z)"
  (* TODO: should be provable by type checker *)
  unfolding Mul_Monoid_def by unfold_types auto


end
