theory Cardinals
  imports
    Coproduct
    Ordinals
    Transport.Functions_Bijection
    Transport.Equivalence_Relations
    Transport.Functions_Surjective
begin

(*TODO Kevin: bundle notation defined in this theory*)
(*TODO Kevin: tag bijection_onE as elim in AFP*)

paragraph \<open>Summary\<close>
text \<open>Translation of equipollence, cardinality and cardinal addition 
from HOL-Library and \<^cite>\<open>ZFC_in_HOL_AFP\<close>.

It illustrates that equipollence is an equivalence relationship and
cardinal addition is commutative and associative. Finally, we derive
the connection between set addition and cardinal addition.\<close>

paragraph \<open>Main Definitions\<close>
text \<open>
\<^item> equipollent
\<^item> cardinality
\<^item> cardinal\_add
\<close>

(*TODO Kevin: move to library*)
lemma inverse_on_if_THE_eq_if_injectice:
  assumes "injective f"
  shows "inverse f (\<lambda>z. THE y. z = f y)"
  using assms injectiveD by fastforce

lemma inverse_on_if_injectice:
  assumes "injective f"
  obtains g where "inverse f g"
  using assms inverse_on_if_THE_eq_if_injectice by blast

unbundle no_HOL_groups_syntax no_HOL_ascii_syntax

paragraph \<open>Equipollence\<close>

text\<open>Equipollence is defined from HOL-Library. 
Two sets \<open>X\<close> and \<open>Y\<close> are said to be equipollent if there
exist two bijections \<open>f\<close> and \<open>g\<close> between them.\<close>

definition "equipollent X Y \<equiv> \<exists>f g. bijection_on (mem_of X) (mem_of Y) (f :: set \<Rightarrow> set) g"

bundle hotg_equipollent_syntax begin notation equipollent (infixl "\<approx>" 50) end
bundle no_hotg_equipollent_syntax begin no_notation equipollent (infixl "\<approx>" 50) end
unbundle hotg_equipollent_syntax

lemma equipollentI [intro]:
  assumes "bijection_on (mem_of X) (mem_of Y) (f :: set \<Rightarrow> set) g"
  shows "X \<approx> Y"
  using assms by (auto simp: equipollent_def)

lemma equipollentE [elim]:
  assumes "X \<approx> Y"
  obtains f g where "bijection_on (mem_of X) (mem_of Y) (f :: set \<Rightarrow> set) g"
  using assms by (auto simp: equipollent_def)

lemma reflexive_equipollent: "reflexive (\<approx>)"
  using bijection_on_self_id by auto

lemma symmetric_equipollent: "symmetric (\<approx>)"
  by (intro symmetricI) (auto dest: bijection_on_right_left_if_bijection_on_left_right)

lemma inverse_on_compI:
  fixes P :: "'a \<Rightarrow> bool" and P' :: "'b \<Rightarrow> bool"
  and f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a" and f' :: "'b \<Rightarrow> 'c" and g' :: "'c \<Rightarrow> 'b"
  assumes "inverse_on P f g"
  and "inverse_on P' f' g'"
  and "([P] \<Rrightarrow>\<^sub>m P') f"
  shows "inverse_on P (f' \<circ> f) (g \<circ> g')"
  using assms by (intro inverse_onI) (auto dest!: inverse_onD)

text\<open>The lemma demonstrates that the composition of two bijections results in another bijection.\<close>

lemma bijection_on_compI:
  fixes P :: "'a \<Rightarrow> bool" and P' :: "'b \<Rightarrow> bool" and P'' :: "'c \<Rightarrow> bool"
  and f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a" and f' :: "'b \<Rightarrow> 'c" and g' :: "'c \<Rightarrow> 'b"
  assumes "bijection_on P P' f g"
  and "bijection_on P' P'' f' g'"
  shows "bijection_on P P'' (f' \<circ> f) (g \<circ> g')"
  using assms by (intro bijection_onI)
  (auto intro: dep_mono_wrt_pred_comp_dep_mono_wrt_pred_compI' inverse_on_compI
    elim!: bijection_onE)

lemma transitive_equipollent: "transitive (\<approx>)"
  by (intro transitiveI) (blast intro: bijection_on_compI)

lemma preorder_equipollent: "preorder (\<approx>)"
  by (intro preorderI transitive_equipollent reflexive_equipollent)

lemma partial_equivalence_rel_equipollent: "partial_equivalence_rel (\<approx>)"
  by (intro partial_equivalence_relI transitive_equipollent symmetric_equipollent)

lemma equivalence_rel_equipollent: "equivalence_rel (\<approx>)"
  by (intro equivalence_relI partial_equivalence_rel_equipollent reflexive_equipollent)

paragraph \<open>Cardinality\<close>

text\<open>Cardinality is defined from \<^cite>\<open>ZFC_in_HOL_AFP\<close>, \<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/ZFC_Cardinals.thy#L1785\<close>.
 The cardinality of a set \<open>X\<close> is defined as the
smallest ordinal number \<open>\<alpha>\<close> such that there 
exists a bijection between \<open>X\<close> and the well-ordered set corresponding to \<open>\<alpha>\<close>.
Further details can be found in \<^cite>\<open>ZFC_in_HOL_AFP\<close>, \<^url>\<open>https://en.wikipedia.org/wiki/Cardinal_number\<close>.\<close>

definition "cardinality (X :: set) \<equiv> (LEAST Y. ordinal Y \<and> X \<approx> Y)"

bundle hotg_cardinality_syntax begin notation cardinality ("|_|") end
bundle no_hotg_cardinality_syntax begin no_notation cardinality ("|_|") end
unbundle hotg_cardinality_syntax

lemma Least_eq_Least_if_iff:
  assumes "\<And>Z. P Z \<longleftrightarrow> Q Z"
  shows "(LEAST Z. P Z) = (LEAST Z. Q Z)"
  using assms by simp

lemma cardinality_eq_if_equipollent:
  assumes "X \<approx> Y"
  shows "|X| = |Y|"
  unfolding cardinality_def using assms transitive_equipollent symmetric_equipollent
  by (intro Least_eq_Least_if_iff) (blast dest: symmetricD)

text\<open>This lemma demonstrates the set \<open>X\<close> is equipollent with the cardinality of \<open>X\<close>.
New order types are necessary to prove it.\<close>

lemma cardinal_equipollent_self [iff]: "|X| \<approx> X"
  sorry

lemma cardinality_cardinality_eq_cardinality [simp]: "||X|| = |X|"
  by (intro cardinality_eq_if_equipollent cardinal_equipollent_self)

paragraph \<open>Cardinal Addition\<close>

text\<open>Cardinal\_add is defined from \<^cite>\<open>ZFC_in_HOL_AFP\<close>, 
\<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/ZFC_Cardinals.thy#L2022\<close>.
The cardinal sum of \<open>\<kappa>\<close> and \<open>\<mu>\<close> is the cardinality of disjoint union of them.\<close>

definition "cardinal_add \<kappa> \<mu> \<equiv> |\<kappa> \<Coprod> \<mu>|"

bundle hotg_cardinal_add_syntax begin notation cardinal_add (infixl "\<oplus>" 65) end
bundle no_hotg_cardinal_add_syntax begin no_notation cardinal_add (infixl "\<oplus>" 65) end
unbundle hotg_cardinal_add_syntax

lemma cardinal_add_eq_cardinality_coprod: "\<kappa> \<oplus> \<mu> = |\<kappa> \<Coprod> \<mu>|"
  unfolding cardinal_add_def ..

lemma equipollent_coprod_self_commute: "X \<Coprod> Y \<approx> Y \<Coprod> X"
  by (intro equipollentI[where ?f="coprod_rec inr inl" and ?g="coprod_rec inr inl"])
  (fastforce dest: inverse_onD)

lemma cardinal_add_comm: "X \<oplus> Y = Y \<oplus> X"
  unfolding cardinal_add_eq_cardinality_coprod
  by (intro cardinality_eq_if_equipollent cardinality_eq_if_equipollent equipollent_coprod_self_commute)

lemma coprod_zero_eqpoll: "{} \<Coprod> X \<approx> X"
  by (intro equipollentI[where ?f="coprod_rec inr id" and ?g="inr"] bijection_onI inverse_onI)
  auto

text\<open>The corallary demonstrates that \<open>0\<close> is the left identity in cardinal addition.\<close>

corollary zero_cardinal_add_eq_cardinality_self: "0 \<oplus> X = |X|"
  unfolding cardinal_add_eq_cardinality_coprod
  by (intro cardinality_eq_if_equipollent coprod_zero_eqpoll)

lemma coprod_assoc_eqpoll: "(X \<Coprod> Y) \<Coprod> Z \<approx> X \<Coprod> (Y \<Coprod> Z)"
proof (intro equipollentI)
   show "bijection_on (mem_of ((X \<Coprod> Y) \<Coprod> Z)) (mem_of (X \<Coprod> (Y \<Coprod> Z)))
      (coprod_rec (coprod_rec inl (inr \<circ> inl)) (inr \<circ> inr))
      (coprod_rec (inl \<circ> inl) (coprod_rec (inl \<circ> inr) inr))"
     by (intro bijection_onI inverse_onI dep_mono_wrt_predI) auto
 qed

lemma cardinality_lift_eq_cardinality_right: "|lift X Y| = |Y|"
proof (intro cardinality_eq_if_equipollent equipollentI)
  let ?f = "\<lambda>z. THE y. y \<in> Y \<and> z = X + y"
  let ?g = "((+) X)"
  from inverse_on_if_injectice show "bijection_on (mem_of (lift X Y)) (mem_of Y) ?f ?g"
    by (intro bijection_onI dep_mono_wrt_predI)
    (auto intro: the1I2 simp: lift_eq_repl_add)
qed

lemma equipollent_bin_union_coprod_if_bin_inter_eq_empty:
  assumes "X \<inter> Y = {}"
  shows "X \<union> Y \<approx> X \<Coprod> Y"
proof -
  let ?l = "\<lambda>z. if z \<in> X then inl z else inr z"
  let ?r = "coprod_rec id id"
  from assms have "bijection_on (mem_of (X \<union> Y)) (mem_of (X \<Coprod> Y)) ?l ?r"
    by (intro bijection_onI dep_mono_wrt_predI inverse_onI) auto
  then show ?thesis by blast
qed

lemma equipollent_coprod_if_equipollent:
  assumes "X \<approx> X'"
  and "Y \<approx> Y'"
  shows "X \<Coprod> Y \<approx> X' \<Coprod> Y'"
proof -
  obtain fX gX fY gY where bijections:
      "bijection_on (mem_of X) (mem_of X') (fX :: set \<Rightarrow> set) gX"
      "bijection_on (mem_of Y) (mem_of Y') (fY :: set \<Rightarrow> set) gY"
    using assms by (elim equipollentE)
  let ?f = "coprod_rec (inl \<circ> fX) (inr \<circ> fY)"
  let ?g = "coprod_rec (inl \<circ> gX) (inr \<circ> gY)"
  have "bijection_on (mem_of (X \<Coprod> Y)) (mem_of (X' \<Coprod> Y')) ?f ?g"
    apply (intro bijection_onI dep_mono_wrt_predI inverse_onI)
    apply (auto elim: mem_coprodE)
    using bijections by (auto intro: elim: mem_coprodE bijection_onE simp: bijection_on_left_right_eq_self
      dest: bijection_on_right_left_if_bijection_on_left_right)
  then show ?thesis by auto
qed

lemma cardinal_add_assoc: "(X \<oplus> Y) \<oplus> Z = X \<oplus> (Y \<oplus> Z)"
proof -
  have "|(X \<Coprod> Y)| \<Coprod> Z \<approx> (X \<Coprod> Y) \<Coprod> Z"
    using reflexive_equipollent by (blast intro: equipollent_coprod_if_equipollent dest: reflexiveD)
  moreover have "... \<approx> X \<Coprod> (Y \<Coprod> Z)" by (simp add: coprod_assoc_eqpoll)
  moreover have "... \<approx> X \<Coprod> |Y \<Coprod> Z|"
    using partial_equivalence_rel_equipollent
    by (blast intro: equipollent_coprod_if_equipollent dest: reflexiveD symmetricD)
  ultimately have "|(X \<Coprod> Y)| \<Coprod> Z \<approx> X \<Coprod> |Y \<Coprod> Z|" using transitive_equipollent by blast
  then show ?thesis
    by (auto intro: cardinality_eq_if_equipollent simp: cardinal_add_eq_cardinality_coprod)
qed

lemma cardinality_bin_union_eq_cardinal_add_if_bin_inter_eq_empty:
  assumes "X \<inter> Y = {}"
  shows "|X \<union> Y| = |X| \<oplus> |Y|"
proof -
  have replacement:"\<And>X. X \<approx> |X|"  
    using  symmetric_equipollent symmetricD[of equipollent] cardinal_equipollent_self
    by auto 
  have cardinalization: "X \<Coprod> Y \<approx> |X| \<Coprod> |Y|"
    using symmetric_equipollent equipollent_coprod_if_equipollent by (force dest: symmetricD)
  from assms have "X \<union> Y \<approx> X \<Coprod> Y" by (intro equipollent_bin_union_coprod_if_bin_inter_eq_empty) auto
  moreover have "... \<approx> |X| \<Coprod> |Y|" 
    using replacement equipollent_coprod_if_equipollent by auto
  ultimately have "X \<union> Y \<approx> |X| \<Coprod> |Y|" using transitiveD[OF transitive_equipollent] by blast
  from cardinal_add_eq_cardinality_coprod have "|X| \<oplus> |Y| = ||X| \<Coprod> |Y||" by simp
  show "|X \<union> Y| = |X| \<oplus> |Y|"
  proof -
    have "X \<union> Y \<approx> |X| \<Coprod> |Y|" 
      using assms cardinalization  equipollent_bin_union_coprod_if_bin_inter_eq_empty 
            transitiveD[OF transitive_equipollent] by blast
    then have "|X \<union> Y| = ||X| \<Coprod> |Y||" using cardinality_eq_if_equipollent by auto
    then show ?thesis by (subst cardinal_add_eq_cardinality_coprod)
        qed
      qed

text\<open>This is a profound theorem that shows the cardinality of the set sum between two sets is 
the cardinal sum of the cardinality of two sets.\<close>

theorem cardinality_add_eq_cardinal_add: "|X + Y| = |X| \<oplus> |Y|"
  using cardinality_lift_eq_cardinality_right
  by (simp add: add_eq_bin_union_lift cardinality_bin_union_eq_cardinal_add_if_bin_inter_eq_empty)

end