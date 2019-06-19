section \<open>Monoids as an example of soft-typed structures\<close>

theory Monoid
imports Structure

begin

text \<open>
Here we define monoids as a structure (though without tool support) and experiment how it
can interact with implicit arguments and type inference.

Structures are modelled as sets that contain the operations, but are parametrized over the carrier
sets.
\<close>

definition Monoid :: "set \<Rightarrow> set type" where
  "Monoid A = element {\<langle>add, neut\<rangle> \<in> (A \<rightarrow> A \<rightarrow> A)\<times>A.
      (\<forall>x\<in>A. add`neut`x = x) \<and>
      (\<forall>x\<in>A. add`x`neut = x) \<and>
      (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. add`(add`x`y)`z = add`x`(add`y`z))}"


text \<open>Here we define monoids using the experimental new structure mechanism.\<close>

struct monoid = "(;; it.
  carrier: non-empty\<cdot>set,
  op: element (it`carrier \<rightarrow> it`carrier \<rightarrow> it`carrier),
  e: element (it`carrier)
where
  \<forall>x \<in> it`carrier. it`op`x`(it`e) = x \<and> it`op`(it`e)`x = x \<and>
  (\<forall>x \<in> it`carrier. \<forall>y \<in> it`carrier. \<forall>z \<in> it`carrier. it`op`x`(it`op`y`z) = it`op`(it`op`x`y)`z)
;;)"

(* The following lemmas should be automatically generated for structures! *)

lemma monoid_carrier_type [intro_st]:
  "M : monoid \<Longrightarrow> M ` carrier : non-empty \<cdot> set"
  unfolding monoid_typedef by stauto

lemma monoid_op_type [intro_st]:
  "M : monoid \<Longrightarrow> M ` op : element (M ` carrier \<rightarrow> M ` carrier \<rightarrow> M ` carrier)"
  unfolding monoid_typedef by stauto

lemma monoid_e_type [intro_st]:
  "M : monoid \<Longrightarrow> M ` e : element (M ` carrier)"
  unfolding monoid_typedef by stauto

lemma monoid_cond1 [intro_st]:
  "\<lbrakk>M : monoid; x \<in> M`carrier\<rbrakk> \<Longrightarrow> M`op`x`(M`e) = x \<and> M`op`(M`e)`x = x"
  unfolding monoid_typedef by stauto

lemma monoid_cond2 [intro_st]:
  "\<lbrakk>M : monoid; x \<in> M`carrier; y \<in> M`carrier; z \<in> M`carrier\<rbrakk> \<Longrightarrow> M`op`x`(M`op`y`z) = M`op`(M`op`x`y)`z"
  unfolding monoid_typedef by stauto


text \<open>
Now we define the global operations as projections. Here, we also convert the set functions
to meta functions. The axioms can then be derived.
\<close>

definition Monoid_add :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set" where
  "Monoid_add M = (%x y. fst M ` x ` y)"

definition Monoid_neut :: "set \<Rightarrow> set" where
  "Monoid_neut M = snd M"

lemma Monoid_neut_type[type]: "Monoid_neut : Monoid A \<Rightarrow> element A"
  by (rule Pi_typeI) (auto simp: Monoid_neut_def Monoid_def element_type_iff)

lemma Monoid_add_type[type]: "Monoid_add : Monoid A \<Rightarrow> element A \<Rightarrow> element A \<Rightarrow> element A"
  apply (intro Pi_typeI) 
  apply (unfold element_type_iff Monoid_add_def Monoid_def)
  apply (drule CollectD1)
  apply (intro PiE; auto?)+
done

lemma
  assumes "M : Monoid A"
  shows 
  Monoid_left_neut: "x \<in> A \<Longrightarrow> Monoid_add M (Monoid_neut M) x = x" and
  Monoid_right_neut: "x \<in> A \<Longrightarrow> Monoid_add M x (Monoid_neut M) = x" and
  Monoid_assoc: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> Monoid_add M (Monoid_add M x y) z = Monoid_add M x (Monoid_add M y z)"

  using assms unfolding Monoid_add_def Monoid_neut_def Monoid_def
  by (auto simp: element_type_iff) blast


text \<open>The same, but for structures:\<close>

definition monoid_add :: "[set, set, set] \<Rightarrow> set" where
  "monoid_add M = (\<lambda>x y. M`op ` x ` y)"

definition monoid_neut :: "set \<Rightarrow> set" where
  "monoid_neut M = M`e"

lemma monoid_neut_type [type]: "monoid_neut : (M : monoid) \<Rightarrow> element (M ` carrier)"
  by (rule Pi_typeI) (simp add: monoid_neut_def monoid_typedef, stauto)

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

definition Group :: "set \<Rightarrow> set type" where
  "Group A = element {\<langle>add, neut, inv\<rangle> \<in> (A \<rightarrow> A \<rightarrow> A)\<times>A\<times>(A \<rightarrow> A).
      \<langle>add,neut\<rangle> : Monoid A \<and> 
      (\<forall>x\<in>A. add`(inv`x)`x = neut) \<and>
      (\<forall>x\<in>A. add`x`(inv`x) = neut)}"

definition to_Monoid :: "set \<Rightarrow> set"
  where
  "to_Monoid G = \<langle>fst G, fst (snd G)\<rangle>"

lemma Group_is_Monoid: "G : Group A \<Longrightarrow> to_Monoid G : Monoid A"
  by (auto simp: element_type_iff to_Monoid_def Group_def)


text \<open>Using structures:\<close>

struct group = "; G.
  inv: element (G`carrier \<rightarrow> G`carrier)
where
  \<forall>g \<in> G`carrier. G`op`(G`inv`g)`g = G`e \<and> G`op`g`(G`inv`g) = G`e
; \<bar> monoid"

lemma group_is_monoid: "group \<prec> monoid"
  unfolding group_typedef by stauto

text \<open>No coercion of structure instances is needed; we simply ignore the fields we don't need.\<close>


end
