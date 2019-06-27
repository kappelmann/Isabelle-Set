section \<open>Monoids as an example of soft-typed structures\<close>

theory Monoid_Structure
imports Structure

begin

text \<open>Here we define monoids using the experimental new structure mechanism.\<close>

struct monoid = "\<lparr> (carrier A) (op op) (e e).
  A: non-empty\<cdot>set \<and>
  op: element (A \<rightarrow> A \<rightarrow> A) \<and>
  e: element A \<and>

  (\<forall>x \<in> A. op`x`e = x \<and> op`e`x = x) \<and>
  (\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A. op`x`(op`y`z) = op`(op`x`y)`z)
\<rparr>"

(* The following lemmas should be automatically generated for structures! *)

lemma monoid_carrier_type [intro_st]:
  "M : monoid \<Longrightarrow> M ` carrier : non-empty \<cdot> set"
  unfolding monoid_typedef by simp
  
lemma monoid_op_type [intro_st]:
  "M : monoid \<Longrightarrow> M ` op : element (M ` carrier \<rightarrow> M ` carrier \<rightarrow> M ` carrier)"
  unfolding monoid_typedef by simp

lemma monoid_e_type [intro_st]:
  "M : monoid \<Longrightarrow> M ` e : element (M ` carrier)"
  unfolding monoid_typedef by simp

lemma monoid_cond1 [intro_st]:
  "\<lbrakk>M : monoid; x \<in> M`carrier\<rbrakk> \<Longrightarrow> M`op`x`(M`e) = x \<and> M`op`(M`e)`x = x"
  unfolding monoid_typedef by auto

lemma monoid_cond2 [intro_st]:
  "\<lbrakk>M : monoid; x \<in> M`carrier; y \<in> M`carrier; z \<in> M`carrier\<rbrakk> \<Longrightarrow> M`op`x`(M`op`y`z) = M`op`(M`op`x`y)`z"
  unfolding monoid_typedef by auto


text \<open>
Now we define the global operations as projections. Here, we also convert the set functions
to meta functions. The axioms can then be derived.
\<close>


definition monoid_add :: "[set, set, set] \<Rightarrow> set" where
  "monoid_add M = (\<lambda>x y. M`op ` x ` y)"

definition monoid_neut :: "set \<Rightarrow> set" where
  "monoid_neut M = M`e"

lemma monoid_neut_type [type]: "monoid_neut : (M : monoid) \<Rightarrow> element (M ` carrier)"
  by (rule Pi_typeI) (simp add: monoid_neut_def, stauto)

lemma monoid_add_type [type]:
  "monoid_add :
    (M : monoid) \<Rightarrow> element (M ` carrier) \<Rightarrow> element (M ` carrier) \<Rightarrow> element (M ` carrier)"
  apply (intro Pi_typeI)
  apply (simp add: monoid_add_def element_type_iff)
  apply (rule PiE; stauto?)
  apply (rule PiE; stauto?)
  apply (fold element_type_iff)
  apply stauto
done

lemma
  assumes "M : monoid"
  shows 
  monoid_left_neut: "x \<in> M ` carrier \<Longrightarrow> monoid_add M (monoid_neut M) x = x" and
  monoid_right_neut: "x \<in> M ` carrier \<Longrightarrow> monoid_add M x (monoid_neut M) = x" and
  monoid_assoc: "x \<in> M ` carrier \<Longrightarrow> y \<in> M ` carrier \<Longrightarrow> z \<in> M ` carrier \<Longrightarrow> monoid_add M (monoid_add M x y) z = monoid_add M x (monoid_add M y z)"

  using assms monoid_cond1 monoid_cond2
  unfolding monoid_add_def monoid_neut_def
  by stauto+
  


subsection \<open>Extension to groups\<close>


struct group = "monoid \<bar> \<lparr> (carrier A) (inv inv) (op op) (e e). 
  inv: element (A \<rightarrow> A) \<and>
  (\<forall>g \<in> A. op`(inv`g)`g = e \<and> op`g`(inv`g) = e) \<rparr>"


lemma group_is_monoid: "group \<prec> monoid"
  unfolding group_typedef by stauto

text \<open>No coercion of structure instances is needed; we simply ignore the fields we don't need.\<close>


end
