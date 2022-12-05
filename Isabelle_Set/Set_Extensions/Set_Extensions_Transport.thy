\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Transport\<close>
theory Set_Extensions_Transport
  imports
    HOL_Basics.Galois
    HOL_Basics.Equivalences
    Set_Extensions_Base
begin

context set_extension
begin

abbreviation (input) "L :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> (=\<^bsub>Rep\<^esub>)"
abbreviation (input) "R :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> (=\<^bsub>Abs\<^esub>)"

sublocale galois L R l r .

(*TODO: somehow the notation for the fixed parameters L and R, defined in
Order_Functions_Base.thy, is lost. We hence re-declare it here.*)
notation L (infix "\<le>\<^bsub>L\<^esub>" 50)
notation R (infix "\<le>\<^bsub>R\<^esub>" 50)

lemma dep_mono_wrt_pred_type_pred_if_Dep_fun_type:
  assumes "g : (x : S) \<Rightarrow> T x"
  shows "([x \<Colon> type_pred S] \<Rrightarrow>\<^sub>m type_pred (T x)) g"
  using assms by (intro dep_mono_wrt_predI) auto

lemma "g : (x : S) \<Rightarrow> T x \<longleftrightarrow> ([x \<Colon> type_pred S] \<Rrightarrow>\<^sub>m type_pred (T x)) g"
  by auto

lemma mono_wrt_rel_if_reflexive_on_if_le_eq_if_mono_wrt_in_field:
  assumes "([in_field N] \<Rrightarrow>\<^sub>m in_field M) g"
  and "N \<le> (=)"
  and "reflexive_on (in_field M) M"
  shows "(N \<Rrightarrow>\<^sub>m M) g"
  using assms by (intro dep_mono_wrt_relI) auto

lemma mono_wrt_rel_left: "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  by (rule mono_wrt_rel_if_reflexive_on_if_le_eq_if_mono_wrt_in_field)
  auto

lemma mono_wrt_rel_right: "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  by (rule mono_wrt_rel_if_reflexive_on_if_le_eq_if_mono_wrt_in_field)
  auto

lemma rel_equivalence_on_unit_iff_inflationary_on_unit_if_inverse_on:
  fixes P :: "'a \<Rightarrow> bool" and N :: "'a \<Rightarrow> _"
  assumes "inverse_on P g h"
  shows "rel_equivalence_on P N (h \<circ> g) \<longleftrightarrow> inflationary_on P N (h \<circ> g)"
  using assms by (intro iffI rel_equivalence_onI inflationary_onI deflationary_onI)
  (auto dest!: inverse_onD)

lemma reflexive_on_if_inflationary_on_unit_if_inverse_on:
  fixes P :: "'a \<Rightarrow> bool" and N :: "'a \<Rightarrow> _"
  assumes "inverse_on P g h"
  and "inflationary_on P N (h \<circ> g)"
  shows "reflexive_on P N"
  using assms by (intro reflexive_onI) (auto dest!: inverse_onD)

lemma rel_equivalence_on_unit_if_reflexive_on_if_inverse_on:
  fixes P :: "'a \<Rightarrow> bool" and N :: "'a \<Rightarrow> _"
  assumes "inverse_on P g h"
  and "reflexive_on P N"
  shows "rel_equivalence_on P N (h \<circ> g)"
  using assms by (intro rel_equivalence_onI inflationary_onI deflationary_onI)
  (auto dest!: inverse_onD)

corollary rel_equivalence_on_unit_iff_reflexive_on_if_inverse_on:
  fixes P :: "'a \<Rightarrow> bool" and N :: "'a \<Rightarrow> _"
  assumes "inverse_on P g h"
  shows "rel_equivalence_on P N (h \<circ> g) \<longleftrightarrow> reflexive_on P N"
  using assms reflexive_on_if_inflationary_on_unit_if_inverse_on
    rel_equivalence_on_unit_if_reflexive_on_if_inverse_on
  by (intro iffI) (auto elim!: rel_equivalence_onE
    simp flip: rel_equivalence_on_unit_iff_inflationary_on_unit_if_inverse_on)

lemma rel_equivalence_on_unit: "rel_equivalence_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  unfolding unit_eq_comp
  using inverse_on_Rep_left_right reflexive_on_eq_restrict
  by (subst rel_equivalence_on_unit_iff_reflexive_on_if_inverse_on)
  simp_all

lemma rel_equivalence_on_counit: "rel_equivalence_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>) \<epsilon>"
  unfolding counit_eq_comp
  using inverse_on_Abs_right_left reflexive_on_eq_restrict
  by (subst rel_equivalence_on_unit_iff_reflexive_on_if_inverse_on)
  simp_all

lemma order_equivalence: "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  using mono_wrt_rel_left mono_wrt_rel_right rel_equivalence_on_unit
    rel_equivalence_on_counit
  by (intro order_equivalenceI)


end


end
