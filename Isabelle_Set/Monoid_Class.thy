section \<open>Monoids as an example of soft-typed structures\<close>

theory Monoid_Class
imports Structure

begin

(*
  This will be subsumed by some generic label mechanism. All we need are labels that we
  know to be distinct from each other
*)
axiomatization
  PLUS ZERO INV :: set
where
  distinct1[simp]: "ZERO \<noteq> PLUS" and
  distinct2[simp]: "PLUS \<noteq> INV" and
  distinct3[simp]: "ZERO \<noteq> INV"


subsection \<open>Plus structures\<close>

definition Plus :: "set \<Rightarrow> set type"
  where Plus_typedef: "Plus A = \<lparr> (PLUS plus). plus : element (A \<rightarrow> A \<rightarrow> A) \<rparr>"

lemma Plus_typeI: "str[PLUS] : element (A \<rightarrow> A \<rightarrow> A) \<Longrightarrow> str : Plus A"
  unfolding Plus_typedef by squash_types

lemma Plus_PLUS_type [derive]: "str: Plus A \<Longrightarrow> str[PLUS] : element (A \<rightarrow> A \<rightarrow> A)"
  unfolding Plus_typedef by squash_types


definition plus :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where "plus p = (\<lambda>x y. p[PLUS] ` x ` y)"

lemma plus_type [type]: "plus : (P : Plus A) \<Rightarrow> element A \<Rightarrow> element A \<Rightarrow> element A"
  unfolding plus_def by discharge_types

abbreviation plus_implicit :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "+" 65)
  where "x + y \<equiv> plus \<implicit>M x y"


subsection \<open>Zero structures\<close>

definition Zero :: "set \<Rightarrow> set type"
  where Zero_typedef: "Zero A = \<lparr> (ZERO z). z : element A \<rparr>"

lemma Zero_typeI: "str[ZERO] : element A \<Longrightarrow> str : Zero A"
  unfolding Zero_typedef by auto

lemma Zero_ZERO_type [derive]: "str: Zero A \<Longrightarrow> str[ZERO] : element A"
  unfolding Zero_typedef by squash_types

definition zero :: "set \<Rightarrow> set"
  where "zero Z = Z[ZERO]"

lemma zero_type [type]: "zero : (Z : Zero A) \<Rightarrow> element A"
  unfolding zero_def by discharge_types

abbreviation zero_implicit :: "set" ("0")
  where "0 \<equiv> zero \<implicit>Z"


text \<open>
  We define monoids as a soft type class (though without tool support) and experiment with
  how it can interact with implicit arguments and type inference.
  
  Structures are modelled as sets that contain the operations, but are parametrized over
  the carrier sets.
\<close>

definition Monoid :: "set \<Rightarrow> set type"
  where Monoid_typedef:
  "Monoid A = Zero A \<bar> Plus A \<bar> \<lparr> (PLUS plus) (ZERO zero) .
    (\<forall>x: element A. plus`zero`x = x) \<and>
    (\<forall>x: element A. plus`x`zero = x) \<and>
    (\<forall>x: element A. \<forall>y: element A. \<forall>z: element A. plus`(plus`x`y)`z = plus`x`(plus`y`z)) \<rparr>"

lemma Monoid_is_Zero [derive]: "Monoid A \<prec> Zero A"
  unfolding Monoid_typedef by (intro subtypeI) squash_types

lemma Monoid_is_Plus [derive]: "Monoid A \<prec> Plus A"
  unfolding Monoid_typedef by (intro subtypeI) squash_types

lemma Monoid_typeI:
  "\<lbrakk>str : Zero A; str : Plus A;
    \<forall>x: element A. str[PLUS]`str[ZERO]`x = x;
    \<forall>x: element A. str[PLUS]`x`str[ZERO] = x;
    \<forall>x: element A. \<forall>y: element A. \<forall>z: element A. 
       str[PLUS]`(str[PLUS]`x`y)`z = str[PLUS]`x`(str[PLUS]`y`z)
    \<rbrakk> \<Longrightarrow> str : Monoid A"
  unfolding Monoid_typedef by squash_types

text \<open>
  Now we define the global operations as projections. Here, we also convert the set
  functions to meta functions. The axioms can then be derived.
\<close>

lemma
  assumes "M : Monoid A"
  shows 
  monoid_left_neut [simp]: "x : element A \<Longrightarrow> plus M (zero M) x = x" and
  monoid_right_neut [simp]: "x : element A \<Longrightarrow> plus M x (zero M) = x" and
  monoid_assoc [simp]: "\<lbrakk>x : element A; y : element A; z : element A\<rbrakk>
     \<Longrightarrow> plus M (plus M x y) z = plus M x (plus M y z)"

  using assms
  unfolding Monoid_typedef Zero_typedef plus_def zero_def
  by (squash_types, blast+)


subsection \<open>An (artificial) instance\<close>



definition
  "pair_plus A B p1 p2 \<equiv>
    \<lparr> PLUS = \<lambda>\<langle>a1,b1\<rangle>\<in>A\<times>B. \<lambda>\<langle>a2,b2\<rangle>\<in>A\<times>B. \<langle>plus p1 a1 a2, plus p2 b1 b2\<rangle> \<rparr>"

definition
  "pair_zero A B z1 z2 \<equiv>
    \<lparr> ZERO = \<langle>zero z1, zero z2\<rangle> \<rparr>"

(* TODO: Need some form of structure composition: pair_monoid = pair_zero [+] pair_plus *)
definition
  "pair_monoid A B m1 m2 \<equiv>
    \<lparr> ZERO = pair_zero A B m1 m2 [ZERO], PLUS = pair_plus A B m1 m2 [PLUS] \<rparr>"

lemma pair_monoid_ZERO [simp]: "pair_monoid A B m1 m2 [ZERO] = pair_zero A B m1 m2 [ZERO]"
  unfolding pair_monoid_def by simp

lemma pair_monoid_PLUS [simp]: "pair_monoid A B m1 m2 [PLUS] = pair_plus A B m1 m2 [PLUS]"
  unfolding pair_monoid_def by simp


text \<open>
  The following proofs illustrate that reasoning with types is still very much pedestrian
  and needs better automated support.
\<close>

lemma pair_plus_PLUS:
  "pair_plus A B p1 p2 [PLUS] = \<lambda>\<langle>a1,b1\<rangle>\<in>A\<times>B. \<lambda>\<langle>a2,b2\<rangle>\<in>A\<times>B. \<langle>plus p1 a1 a2, plus p2 b1 b2\<rangle>"
  unfolding pair_plus_def by auto

lemma pair_plus_type [type]:
  "pair_plus : (A : set) \<Rightarrow> (B : set) \<Rightarrow> Plus A \<Rightarrow> Plus B \<Rightarrow> Plus (A \<times> B)"
  apply (intro Pi_typeI Plus_typeI)
  apply (unfold pair_plus_PLUS split_def)
  by discharge_types

lemma pair_zero_type [type]:
  "pair_zero : (A : set) \<Rightarrow> (B : set) \<Rightarrow> Zero A \<Rightarrow> Zero B \<Rightarrow> Zero (A \<times> B)"
  unfolding Zero_typedef pair_zero_def zero_def
  by squash_types auto

setup \<open>soft_type_simp_solver\<close>


lemma pair_monoid_type [type]:
  "pair_monoid : (A : set) \<Rightarrow> (B : set) \<Rightarrow> Monoid A \<Rightarrow> Monoid B \<Rightarrow> Monoid (A \<times> B)"
proof (intro Pi_typeI)
  fix A B p1 p2
  assume [intro, type]: "A : set" "B : set" "p1 : Monoid A" "p2 : Monoid B"
  have [intro, type]: "p1 : Zero A" "p1 : Plus A" "p2 : Zero B" "p2 : Plus B"
    by (auto intro: Monoid_is_Plus[THEN subtypeE'] Monoid_is_Zero[THEN subtypeE'])

  note zero_type[THEN Pi_typeE, unfolded element_type_iff, intro]
  note plus = plus_type[THEN Pi_typeE, THEN Pi_typeE, THEN Pi_typeE, unfolded element_type_iff, intro]

  let ?plus_pair = "pair_monoid A B p1 p2 [PLUS]"
  let ?zero_pair = "pair_monoid A B p1 p2 [ZERO]"

  show "pair_monoid A B p1 p2 : Monoid (A \<times> B)" 
  proof (rule Monoid_typeI)

    show "pair_monoid A B p1 p2 : Zero (A \<times> B)"
      by (rule Zero_typeI) (auto simp: pair_zero_def element_type_iff)
    show "pair_monoid A B p1 p2 : Plus (A \<times> B)"
      by (rule Plus_typeI)
        (auto simp: pair_plus_def element_type_iff intro!: plus `p1 : Plus A` `p2 : Plus B` Pi_lambdaI)

    show "\<forall>x: element (A \<times> B). ?plus_pair ` ?zero_pair ` x = x"
      unfolding split_paired_ball
      by (auto simp: pair_monoid_def pair_plus_def pair_zero_def)

    show "\<forall>x: element (A \<times> B). ?plus_pair ` x ` ?zero_pair = x"
      unfolding split_paired_ball
        by (auto simp: pair_monoid_def pair_plus_def pair_zero_def)

    show "\<forall>x: element (A\<times>B). \<forall>y: element (A\<times>B). \<forall>z: element (A\<times>B). 
  ?plus_pair ` (?plus_pair ` x ` y) ` z = ?plus_pair ` x ` (?plus_pair ` y ` z)"
      unfolding split_paired_ball
      by (auto simp: pair_monoid_def pair_plus_def pair_zero_def)
  qed

qed
  
lemma [type_instance]:
  "m1 : Plus A \<Longrightarrow> m2 : Plus B \<Longrightarrow> pair_plus A B m1 m2 : Plus (A \<times> B)"
  "m1 : Zero A \<Longrightarrow> m2 : Zero B \<Longrightarrow> pair_zero A B m1 m2 : Zero (A \<times> B)"
  "m1 : Monoid A \<Longrightarrow> m2 : Monoid B \<Longrightarrow> pair_monoid A B m1 m2 : Monoid (A \<times> B)"
  by discharge_types


declare [[auto_elaborate, trace_soft_types]]

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




subsection \<open>Extension to groups\<close>

declare [[auto_elaborate = false]]
definition Group :: "set \<Rightarrow> set type"
  where Group_typedef:
  "Group A = Monoid A \<bar> \<lparr> (PLUS plus) (ZERO zero) (INV inv).
     inv : element (A \<rightarrow> A) \<and>
     (\<forall>x\<in>A. plus`(inv`x)`x = zero) \<and>
     (\<forall>x\<in>A. plus`x`(inv`x) = zero) \<rparr>"

lemma group_is_monoid:  "G : Group A \<Longrightarrow> G : Monoid A"
  unfolding Group_typedef by squash_types


end
