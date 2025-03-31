\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Evaluation of Set-Theoretic Functions\<close>
theory HOTG_Functions_Evaluation
  imports
    HOTG_Binary_Relations_Right_Unique
    HOTG_Binary_Relations_Extend
    Transport.Binary_Relations_Function_Evaluation
begin

unbundle no HOL_ascii_syntax

subsubsection \<open>Evaluation\<close>

definition "eval_set R \<equiv> eval (rel R)"
adhoc_overloading eval \<rightleftharpoons> eval_set

lemma eval_set_eq_eval_rel [simp, set_to_HOL_simp]: "(R :: set)`x = (rel R)`x"
  unfolding eval_set_def by simp

lemma eval_set_eq_eval_rel_uhint [uhint]:
  assumes "S \<equiv> rel R"
  and "x \<equiv> y"
  shows "(R :: set)`x = S`y"
  using assms by simp

context
  notes set_to_HOL_simp[simp, uhint, symmetric, simp del]
  fixes R :: set
begin

lemma eval_set_eq_if_right_unique_on_singletonI:
  assumes "right_unique_on {x} R"
  and "\<langle>x, y\<rangle> \<in> R"
  shows "R`x = y"
  using assms by (urule eval_eq_if_right_unique_on_eqI)

lemma pair_eval_mem_if_mem_dom_if_right_unique_on:
  assumes "right_unique_on {x} R"
  and "x \<in> dom R"
  shows "\<langle>x, R`x\<rangle> \<in> R"
  using assms by (urule rel_eval_if_in_dom_if_right_unique_on_eq)

lemma glue_set_eval_eqI:
  assumes "right_unique_on P (glue \<R>)"
  and [uhint]: "R \<in> \<R>"
  and "P x"
  and "\<langle>x, y\<rangle> \<in> R"
  shows "(glue \<R>)`x = y"
  supply has_inverse_onI[rec_uhint] using assms by (urule glue_eval_eqI)

lemma glue_set_eval_eq_evalI:
  assumes "right_unique_on P (glue \<R>)"
  and [uhint]: "R \<in> \<R>"
  and "P x"
  and "x \<in> dom R"
  shows "(glue \<R>)`x = R`x"
  supply has_inverse_onI[rec_uhint] using assms by (urule glue_eval_eq_evalI)

lemma extend_set_eval_eq_if_not_mem_dom [simp]:
  assumes "x \<notin> dom R"
  shows "(extend x y R)`x = y"
  using assms by (urule extend_eval_eq_if_not_in_dom)

lemma extend_empty_eval_eq [simp]: "(extend x y {})`x = y"
  by (urule extend_bottom_eval_eq)

lemma extend_set_eval_eq_if_neq [simp]:
  assumes "x \<noteq> y"
  shows "(extend y z R)`x = R`x"
  using assms by (urule extend_eval_eq_if_neq)

lemma bin_union_eval_eq_left_eval_if_not_mem_dom [simp]:
  assumes "x \<notin> dom S"
  shows "(R \<union> S)`x = R`x"
  using assms by (urule sup_eval_eq_left_eval_if_not_in_dom)

lemma bin_union_eval_eq_right_eval_if_not_mem_dom [simp]:
  assumes "x \<notin> dom R"
  shows "(R \<union> S)`x = S`x"
  using assms by (urule sup_eval_eq_right_eval_if_not_in_dom)

lemma set_rel_restrict_left_eval_eq_if_pred [simp]:
  assumes "P x"
  shows "(R\<restriction>\<^bsub>P\<^esub>)`x = R`x"
  using assms by (urule rel_restrict_left_eval_eq_if_pred)

end

lemma repl_eval_eq_if_mem [simp]:
  assumes "x \<in> A"
  shows "{\<langle>a, f a\<rangle> | a \<in> A}`x = f x"
  using assms by (auto intro: eval_eq_if_right_unique_onI)


end