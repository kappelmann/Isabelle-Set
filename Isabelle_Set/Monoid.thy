section \<open>Monoids as an example of soft-typed structures\<close>

theory Monoid
imports Function

begin

text \<open>
  We define monoids as a structure (though without tool support) and experiment how it can interact
  with implicit arguments and type inference.

  Structures are modelled as sets that contain the operations, but are parametrized over the carrier
  sets.  
\<close>

definition Monoid_Set :: "set \<Rightarrow> set" where
  "Monoid_Set A = {\<langle>add, neut\<rangle> \<in> (A \<rightarrow> A \<rightarrow> A)\<times>A. 
      (\<forall>x\<in>A. add`neut`x = x) \<and>
      (\<forall>x\<in>A. add`x`neut = x) \<and>
      (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. add`(add`x`y)`z = add`x`(add`y`z))}"

abbreviation Monoid :: "set \<Rightarrow> set type" where
  "Monoid A \<equiv> element (Monoid_Set A)"


text \<open>
  Now we define the global operations as projections. Here, we also convert the set functions
  to meta functions. The axioms can then be derived.
\<close>

definition monoid_add :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set" where
  "monoid_add M = (%x y. fst M ` x ` y)"

definition monoid_neut :: "set \<Rightarrow> set" where
  "monoid_neut M = snd M"

lemma monoid_neut_type[type]: "monoid_neut : Monoid A \<Rightarrow> element A"
  by (rule Pi_typeI) (auto simp: monoid_neut_def Monoid_Set_def element_type_iff)

lemma monoid_add_type[type]: "monoid_add : Monoid A \<Rightarrow> element A \<Rightarrow> element A \<Rightarrow> element A"
  apply (intro Pi_typeI) 
  apply (unfold element_type_iff monoid_add_def Monoid_Set_def)
  apply (drule CollectD)
  apply (intro funE)
  apply auto
done
 

lemma
  assumes "M : Monoid A"
  shows 
  monoid_left_neut: "x \<in> A \<Longrightarrow> monoid_add M (monoid_neut M) x = x" and
  monoid_right_neut: "x \<in> A \<Longrightarrow> monoid_add M x (monoid_neut M) = x" and
  monoid_assoc: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> monoid_add M (monoid_add M x y) z = monoid_add M x (monoid_add M y z)"

  using assms unfolding monoid_add_def monoid_neut_def Monoid_Set_def
  by (auto simp: element_type_iff) blast



subsection \<open>Extension to Group\<close>

definition Group_Set :: "set \<Rightarrow> set" where
  "Group_Set A = {\<langle>add, neut, inv\<rangle> \<in> (A \<rightarrow> A \<rightarrow> A)\<times>A\<times>(A \<rightarrow> A).
      \<langle>add,neut\<rangle> : Monoid A \<and> 
      (\<forall>x\<in>A. add`(inv`x)`x = neut) \<and>
      (\<forall>x\<in>A. add`x`(inv`x) = neut)}"

abbreviation Group :: "set \<Rightarrow> set type" where
  "Group A \<equiv> element (Group_Set A)"



definition to_monoid :: "set \<Rightarrow> set"
  where
  "to_monoid G = \<langle>fst G, fst (snd G)\<rangle>"

lemma group_is_monoid:  "G : Group A \<Longrightarrow> to_monoid G : Monoid A"
  by (auto simp: element_type_iff to_monoid_def Group_Set_def)



end
