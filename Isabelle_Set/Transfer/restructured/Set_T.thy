theory Set_T
  imports Basic_T HOTG.Bounded_Quantifiers
begin

definition bijection :: "set \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool"
  where "bijection A B f g \<equiv> (\<forall>x\<in>A. f x \<in> B) \<and> (\<forall>y\<in>B. g y \<in> A) \<and> (\<forall>x\<in>A. g (f x) = x) \<and> (\<forall>y\<in>B. f (g y) = y)"

lemma bijectionI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> B"
      and "\<And>y. y \<in> B \<Longrightarrow> g y \<in> A"
      and "\<And>x. x \<in> A \<Longrightarrow> g (f x) = x"
      and "\<And>y. y \<in> B \<Longrightarrow> f (g y) = y"
    shows "bijection A B f g"
  using assms
  unfolding bijection_def by blast

lemma bijection_inv1: "bijection A B f g \<Longrightarrow> x \<in> A \<Longrightarrow> g (f x) = x"
  unfolding bijection_def by blast

lemma bijection_inv2: "bijection A B f g \<Longrightarrow> y \<in> B \<Longrightarrow> f (g y) = y"
  unfolding bijection_def by blast

lemma bijection_map_mem1: "bijection A B f g \<Longrightarrow> x \<in> A \<Longrightarrow> f x \<in> B"
  unfolding bijection_def by blast

lemma bijection_map_mem2: "bijection A B f g \<Longrightarrow> y \<in> B \<Longrightarrow> g y \<in> A"
  unfolding bijection_def by blast

definition Iso_Rel :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
  where "Iso_Rel A f x y \<equiv> x \<in> A \<and> f x = y"

lemma Iso_RelI: "\<lbrakk>x \<in> A; f x = y\<rbrakk> \<Longrightarrow> Iso_Rel A f x y"
  unfolding Iso_Rel_def by simp

lemma Iso_Rel_mem: "Iso_Rel A f x y \<Longrightarrow> x \<in> A"
  unfolding Iso_Rel_def by simp

lemma Iso_Rel_map: "Iso_Rel A f x y \<Longrightarrow> f x = y"
  unfolding Iso_Rel_def by simp

lemma z_property_Iso_Rel: "z_property (Iso_Rel A f)"
  apply (rule z_propertyI)
  unfolding Iso_Rel_def by simp

lemma in_dom_Iso_Rel_if_mem: "in_dom (Iso_Rel A f) x = (x \<in> A)"
proof (rule iffI)
  assume in_dom_x: "in_dom (Iso_Rel A f) x"
  show "x \<in> A"
    using Iso_Rel_mem[of A f x] in_domE[OF in_dom_x]
    by blast
next
  assume x_in_A: "x \<in> A"
  show "in_dom (Iso_Rel A f) x"
    using in_domI[of "Iso_Rel A f"] Iso_RelI x_in_A by blast
qed

(* required? *)
lemma in_co_dom_Iso_Rel_if_ex: "in_co_dom (Iso_Rel A f) y = (\<exists>x\<in>A. f x = y)"
proof (rule iffI)
  assume in_co_dom_y: "in_co_dom (Iso_Rel A f) y"
  obtain x where "Iso_Rel A f x y"
    using in_co_domE in_co_dom_y .
  thus "\<exists>x \<in> A. f x = y"
    using Iso_Rel_mem Iso_Rel_map by blast
next
  assume "\<exists>x \<in> A. f x = y"
  thus "in_co_dom (Iso_Rel A f) y"
    using in_co_domI[of "Iso_Rel A f", OF Iso_RelI] by blast
qed

lemma bijection_transfer_triple:
  assumes biject: "bijection A B f g"
  shows "transfer_triple (Iso_Rel A f) f g"
proof (rule transfer_tripleI)
  show "z_property (Iso_Rel A f)"
    using z_property_Iso_Rel .
next
  fix x
  assume in_dom_x: "in_dom (Iso_Rel A f) x"
  show "Iso_Rel A f x (f x)"
    using Iso_RelI in_dom_Iso_Rel_if_mem in_dom_x by blast
next
  fix y
  assume in_co_dom_y: "in_co_dom (Iso_Rel A f) y"
  obtain x where "Iso_Rel A f x y"
    using in_co_domE in_co_dom_y .
  hence "x \<in> A" "f x = y"
    using Iso_Rel_mem Iso_Rel_map by blast+
  hence 1: "y \<in> B"
    using bijection_map_mem1 biject by blast
  show "Iso_Rel A f (g y) y"
    apply (rule Iso_RelI)
    using 1 bijection_map_mem2 bijection_inv2 biject by blast+
qed

definition Eq_Rel :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
  where "Eq_Rel A \<equiv> Iso_Rel A id"

lemma Eq_RelI: "x \<in> A \<Longrightarrow> Eq_Rel A x x"
  unfolding Eq_Rel_def
  apply (rule Iso_RelI)
  by (assumption, rule id_apply)

lemma Eq_Rel_elem: "Eq_Rel A x y \<Longrightarrow> x \<in> A"
  unfolding Eq_Rel_def
  by (fact Iso_Rel_mem)

lemma Eq_Rel_eq: "Eq_Rel A x y \<Longrightarrow> x = y"
  unfolding Eq_Rel_def
  apply (drule Iso_Rel_map) by simp

(* required? *)
lemma partial_equivalence_Eq_Rel: "partial_equivalence (Eq_Rel A)"
  apply (rule partial_equivalenceI)
  using Eq_RelI Eq_Rel_elem Eq_Rel_eq by blast+

lemma bijection_id: "bijection A A id id"
  apply (rule bijectionI) by simp+

lemma id_transfer_triple: "transfer_triple (Eq_Rel A) id id"
  unfolding Eq_Rel_def
  apply (rule bijection_transfer_triple)
  using bijection_id .

end