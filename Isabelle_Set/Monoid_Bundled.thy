section \<open>Monoids as an example of soft-typed bundled structures\<close>

theory Monoid_Bundled
imports Object

begin

text \<open>Here we define monoids using the experimental new structure mechanism.\<close>

object monoid is "\<lparr> (A @carrier) (op @op) (e @unit).
  A: non-empty\<sqdot>set \<and>
  op: element (A \<rightarrow> A \<rightarrow> A) \<and>
  e: element A \<and>

  (\<forall>x \<in> A. op`x`e = x \<and> op`e`x = x) \<and>
  (\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A. op`x`(op`y`z) = op`(op`x`y)`z)
\<rparr>"

thm monoid_typedef

(* The following lemmas should be automatically generated for structures! *)

lemma monoid_carrier_type:
  "M : monoid \<Longrightarrow> M[@carrier] : non-empty \<sqdot> set"
  unfolding monoid_typedef by simp
  
lemma monoid_op_type:
  "M : monoid \<Longrightarrow> M[@op] : element (M[@carrier] \<rightarrow> M[@carrier] \<rightarrow> M[@carrier])"
  unfolding monoid_typedef by simp

lemma monoid_e_type:
  "M : monoid \<Longrightarrow> M[@unit] : element (M[@carrier])"
  unfolding monoid_typedef by simp

lemma monoid_cond1:
  "\<lbrakk>M : monoid; x \<in> M[@carrier]\<rbrakk> \<Longrightarrow> M[@op]`x`(M[@unit]) = x \<and> M[@op]`M[@unit]`x = x"
  unfolding monoid_typedef by auto

lemma monoid_cond2:
  "\<lbrakk>M : monoid; x \<in> M[@carrier]; y \<in> M[@carrier]; z \<in> M[@carrier]\<rbrakk>
    \<Longrightarrow> M[@op]`x`(M[@op]`y`z) = M[@op]`(M[@op]`x`y)`z"
  unfolding monoid_typedef by auto


text \<open>
Now we define the global operations as projections. Here, we also convert the set functions
to meta functions. The axioms can then be derived.
\<close>

definition monoid_add :: "[set, set, set] \<Rightarrow> set" where
  "monoid_add M = (\<lambda>x y. M[@op] ` x ` y)"

definition monoid_neut :: "set \<Rightarrow> set" where
  "monoid_neut M = M[@unit]"

lemma monoid_neut_type [type]: "monoid_neut : (M : monoid) \<Rightarrow> element (M[@carrier])"
  unfolding monoid_neut_def monoid_typedef by auto

lemma monoid_add_type [type]:
  "monoid_add :
    (M : monoid) \<Rightarrow> element (M[@carrier]) \<Rightarrow> element (M[@carrier]) \<Rightarrow> element (M[@carrier])"
  unfolding monoid_typedef monoid_add_def by squash_types (auto intro: FunctionE)

lemma
  assumes "M : monoid"
  shows 
  monoid_left_neut: "x \<in> M[@carrier] \<Longrightarrow> monoid_add M (monoid_neut M) x = x" and
  monoid_right_neut: "x \<in> M[@carrier] \<Longrightarrow> monoid_add M x (monoid_neut M) = x" and
  monoid_assoc: "\<lbrakk>x \<in> M[@carrier]; y \<in> M[@carrier]; z \<in> M[@carrier]\<rbrakk>
    \<Longrightarrow> monoid_add M (monoid_add M x y) z = monoid_add M x (monoid_add M y z)"

  using assms monoid_cond1 monoid_cond2
  unfolding monoid_add_def monoid_neut_def
  by auto
  

subsection \<open>Extension to groups\<close>


object group is "monoid \<bar> \<lparr> (A @carrier) (inv @inv) (op @op) (e @unit). 
  inv: element (A \<rightarrow> A) \<and>
  (\<forall>g \<in> A. op`(inv`g)`g = e \<and> op`g`(inv`g) = e) \<rparr>"


lemma group_is_monoid: "group \<prec> monoid"
  unfolding group_typedef by (intro subtypeI) squash_types

text \<open>No coercion of structure instances is needed; we simply ignore the fields we don't need.\<close>


end
