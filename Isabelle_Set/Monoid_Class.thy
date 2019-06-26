section \<open>Monoids as an example of soft-typed structures\<close>

theory Monoid_Class
imports Function

begin

text \<open>
  We define monoids as a soft type class (though without tool support) and experiment how it can interact
  with implicit arguments and type inference.

  Structures are modelled as sets that contain the operations, but are parametrized over the carrier
  sets.  
\<close>

definition Monoid :: "set \<Rightarrow> set type" where
  "Monoid A = element {\<langle>add, neut\<rangle> \<in> (A \<rightarrow> A \<rightarrow> A)\<times>A. 
      (\<forall>x\<in>A. add`neut`x = x) \<and>
      (\<forall>x\<in>A. add`x`neut = x) \<and>
      (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. add`(add`x`y)`z = add`x`(add`y`z))}"


text \<open>
  Now we define the global operations as projections. Here, we also convert the set functions
  to meta functions. The axioms can then be derived.
\<close>

definition monoid_add :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set" where
  "monoid_add M = (%x y. fst M ` x ` y)"

definition monoid_neut :: "set \<Rightarrow> set" where
  "monoid_neut M = snd M"

lemma monoid_neut_type[type]: "monoid_neut : (M : Monoid A) \<Rightarrow> element A"
  by (rule Pi_typeI) (auto simp: monoid_neut_def Monoid_def element_type_iff)

lemma monoid_add_type[type]: "monoid_add : (M : Monoid A) \<Rightarrow> element A \<Rightarrow> element A \<Rightarrow> element A"
  apply (intro Pi_typeI) 
  apply (unfold element_type_iff monoid_add_def Monoid_def)
  apply (drule CollectD1)
  apply (intro PiE; auto?)+
done
 

lemma
  assumes "M : Monoid A"
  shows 
  monoid_left_neut: "x \<in> A \<Longrightarrow> monoid_add M (monoid_neut M) x = x" and
  monoid_right_neut: "x \<in> A \<Longrightarrow> monoid_add M x (monoid_neut M) = x" and
  monoid_assoc: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> monoid_add M (monoid_add M x y) z = monoid_add M x (monoid_add M y z)"

  using assms unfolding monoid_add_def monoid_neut_def Monoid_def
  by (auto simp: element_type_iff) blast



subsection \<open>An (artificial) instance\<close>



consts
  Nat :: set
  zero :: set
  plus :: set


definition
  "Nat_monoid \<equiv> \<langle>plus, zero\<rangle>"

axiomatization (* TODO derive this *)
where Nat_monoid[type_instance]: "Nat_monoid : Monoid Nat"


definition
  "pair_monoid A B m1 m2 \<equiv> \<langle>\<lambda>\<langle>a1,b1\<rangle>\<in>A\<times>B. \<lambda>\<langle>a2,b2\<rangle>\<in>A\<times>B. \<langle>monoid_add m1 a1 a2, monoid_add m2 b1 b2\<rangle>,
     \<langle>monoid_neut m1, monoid_neut m2\<rangle>\<rangle>"

axiomatization (* TODO derive this *)
where pair_monoid_type[type]:
  "pair_monoid : (A : set) \<Rightarrow> (B : set) \<Rightarrow> Monoid A \<Rightarrow> Monoid B \<Rightarrow> Monoid (A \<times> B)"

lemma pair_monoid_instance[type_instance]:
  "m1 : Monoid A \<Longrightarrow> m2 : Monoid B \<Longrightarrow> pair_monoid A B m1 m2 : Monoid (A \<times> B)"
  by (rule pair_monoid_type[THEN Pi_typeE, THEN Pi_typeE, THEN Pi_typeE, THEN Pi_typeE]) auto


abbreviation monoid_add_implicit :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "+" 60)
  where
  "monoid_add_implicit x y \<equiv> monoid_add \<implicit>M x y"


declare monoid_neut_type[type implicit: 1]
declare monoid_add_type[type implicit: 1]


declare [[auto_elaborate, trace_soft_types]]

lemma "monoid_add monoid_neut \<langle>x, y\<rangle> = \<langle>x, y\<rangle>"
  oops

lemma "x + (y + z) = x + y + z"
  oops

lemma "x + y = z + w \<and> u + v = monoid_neut"
  oops



declare [[auto_elaborate = false]]


subsection \<open>Extension to Group\<close>

definition Group :: "set \<Rightarrow> set type" where
  "Group A = element {\<langle>add, neut, inv\<rangle> \<in> (A \<rightarrow> A \<rightarrow> A)\<times>A\<times>(A \<rightarrow> A).
      \<langle>add,neut\<rangle> : Monoid A \<and> 
      (\<forall>x\<in>A. add`(inv`x)`x = neut) \<and>
      (\<forall>x\<in>A. add`x`(inv`x) = neut)}"



definition to_monoid :: "set \<Rightarrow> set"
  where
  "to_monoid G = \<langle>fst G, fst (snd G)\<rangle>"

lemma group_is_monoid:  "G : Group A \<Longrightarrow> to_monoid G : Monoid A"
  by (auto simp: element_type_iff to_monoid_def Group_def)



end
