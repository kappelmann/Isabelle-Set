\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Addition\<close>
theory HOTG_Cardinals_Addition
  imports
    HOTG_Cardinals_Base
    HOTG_Coproduct
begin

unbundle no HOL_groups_syntax

paragraph \<open>Summary\<close>
text \<open>Cardinal addition is the cardinality of the disjoint union of two sets.
We show that cardinal addition is commutative and associative.
We also derive the connection between set addition and cardinal addition.\<close>

definition "cardinal_add X Y \<equiv> |X \<Coprod> Y|"

open_bundle hotg_cardinal_add_syntax begin notation cardinal_add (infixl "\<oplus>" 65) end

lemma cardinal_add_eq_cardinality_coprod: "X \<oplus> Y = |X \<Coprod> Y|"
  unfolding cardinal_add_def ..

lemma coprod_equipollent_self_commute: "X \<Coprod> Y \<approx> Y \<Coprod> X"
  by (intro equipollentI[where ?f="coprod_rec inr inl" and ?g="coprod_rec inr inl"])
  fastforce

lemma cardinal_add_comm: "X \<oplus> Y = Y \<oplus> X"
  unfolding cardinal_add_eq_cardinality_coprod
  by (intro cardinality_eq_if_equipollent coprod_equipollent_self_commute)

lemma empty_coprod_equipollent_self: "{} \<Coprod> X \<approx> X"
  by (intro equipollentI[where ?f="coprod_rec inr id" and ?g="inr"])
  fastforce

text\<open>\<open>0\<close> is the neutral element for cardinal addition.\<close>

corollary zero_cardinal_add_eq_cardinality_self: "0 \<oplus> X = |X|"
  unfolding cardinal_add_eq_cardinality_coprod
  by (intro cardinality_eq_if_equipollent empty_coprod_equipollent_self)

lemma coprod_equipollent_assoc: "(X \<Coprod> Y) \<Coprod> Z \<approx> X \<Coprod> (Y \<Coprod> Z)"
proof (rule equipollentI)
   show "bijection_on ((X \<Coprod> Y) \<Coprod> Z :: set) (X \<Coprod> (Y \<Coprod> Z))
      (coprod_rec (coprod_rec inl (inr \<circ> inl)) (inr \<circ> inr))
      (coprod_rec (inl \<circ> inl) (coprod_rec (inl \<circ> inr) inr))"
    by (urule (rr) bijection_onI dep_mono_wrt_predI inverse_onI) fastforce+
qed

lemma coprod_equipollent_if_equipollent:
  assumes "X \<approx> X'"
  and "Y \<approx> Y'"
  shows "X \<Coprod> Y \<approx> X' \<Coprod> Y'"
proof -
  from assms obtain fX gX fY gY where bijections:
    "bijection_on X X' (fX :: set \<Rightarrow> set) (gX :: set \<Rightarrow> set)"
    "bijection_on Y Y' (fY :: set \<Rightarrow> set) (gY :: set \<Rightarrow> set)"
    by (elim equipollentE)
  let ?f = "coprod_rec (inl \<circ> fX) (inr \<circ> fY)"
  let ?g = "coprod_rec (inl \<circ> gX) (inr \<circ> gY)"
  have "bijection_on (X \<Coprod> Y :: set) (X' \<Coprod> Y') ?f ?g"
    by (urule (rr) bijection_onI mono_wrt_predI inverse_onI)
    (use bijections in \<open>auto 0 4 simp: bijection_on_left_right_eq_self
      dest: bijection_on_right_left_if_bijection_on_left_right\<close>)
  then show ?thesis by auto
qed

corollary cardinality_coprod_equipollent_coprod [iff]: "|X| \<Coprod> |Y| \<approx> X \<Coprod> Y"
  using coprod_equipollent_if_equipollent by auto

corollary cardinality_cardinal_add_eq_cardinal_add [simp]: "|X| \<oplus> |Y| = X \<oplus> Y"
  unfolding cardinal_add_eq_cardinality_coprod
  by (intro cardinality_eq_if_equipollent cardinality_coprod_equipollent_coprod)

lemma cardinal_add_assoc: "(X \<oplus> Y) \<oplus> Z = X \<oplus> (Y \<oplus> Z)"
proof -
  have "|(X \<Coprod> Y)| \<Coprod> Z \<approx> (X \<Coprod> Y) \<Coprod> Z"
    using reflexive_equipollent by (blast intro: coprod_equipollent_if_equipollent dest: reflexiveD)
  moreover have "... \<approx> X \<Coprod> (Y \<Coprod> Z)" by (simp add: coprod_equipollent_assoc)
  moreover have "... \<approx> X \<Coprod> |Y \<Coprod> Z|" using partial_equivalence_rel_equipollent
    by (blast intro: coprod_equipollent_if_equipollent dest: reflexiveD symmetricD)
  ultimately have "|(X \<Coprod> Y)| \<Coprod> Z \<approx> X \<Coprod> |Y \<Coprod> Z|" using transitive_equipollent by blast
  then show ?thesis
    by (auto intro: cardinality_eq_if_equipollent simp: cardinal_add_eq_cardinality_coprod)
qed

lemma bin_union_equipollent_coprod_if_disjoint:
  assumes "disjoint X Y"
  shows "X \<union> Y \<approx> X \<Coprod> Y"
proof -
  let ?l = "\<lambda>z. if z \<in> X then inl z else inr z"
  let ?r = "coprod_rec id id"
  from assms have "bijection_on (mem_of (X \<union> Y)) (mem_of (X \<Coprod> Y)) ?l ?r"
    by (intro bijection_onI mono_wrt_predI inverse_onI) auto
  then show ?thesis by blast
qed

corollary cardinality_bin_union_eq_cardinal_add_if_disjoint:
  assumes "disjoint X Y"
  shows "|X \<union> Y| = X \<oplus> Y"
  unfolding cardinal_add_eq_cardinality_coprod using assms
  by (intro cardinality_eq_if_equipollent bin_union_equipollent_coprod_if_disjoint)

end
