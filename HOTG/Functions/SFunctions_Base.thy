\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Evaluation of Functions\<close>
theory SFunctions_Base
  imports
    SBinary_Relations_Right_Unique
    SBinary_Relations_Left_Total
begin

definition "eval f x \<equiv> THE y. \<langle>x, y\<rangle> \<in> f"

bundle hotg_eval_syntax begin notation eval ("_`_" [999, 1000] 999) end
bundle no_hotg_eval_syntax begin no_notation eval ("_`_" [999, 1000] 999) end
unbundle hotg_eval_syntax

lemma eval_eqI:
  assumes "set_right_unique_on P f"
  and "P x"
  and "\<langle>x, y\<rangle> \<in> f"
  shows "f`x = y"
  using assms unfolding eval_def by (auto dest: set_right_unique_onD)

lemma eval_eqI':
  assumes "set_right_unique_on {x} f"
  and "\<langle>x, y\<rangle> \<in> f"
  shows "f`x = y"
  using assms by (auto intro: eval_eqI)

lemma pair_eval_mem_if_ex1_pair_mem:
  assumes "\<exists>!y. \<langle>x, y\<rangle> \<in> f"
  shows "\<langle>x, f`x\<rangle> \<in> f"
  using assms unfolding eval_def by (rule theI')

lemma pair_eval_mem_if_mem_dom_if_set_right_unique_on:
  assumes "set_right_unique_on {x} f"
  and "x \<in> dom f"
  shows "\<langle>x, f`x\<rangle> \<in> f"
  using assms
  by (intro pair_eval_mem_if_ex1_pair_mem) (auto dest: set_right_unique_onD)

lemma eval_singleton_eq [simp]: "{\<langle>x, y\<rangle>}`x = y"
  by (rule eval_eqI) auto

lemma eval_repl_eq [iff]: "x \<in> A \<Longrightarrow> {\<langle>a, f a\<rangle> | a \<in> A}`x = f x"
  by (auto intro: eval_eqI)

lemma extend_eval_eq [simp]: "x \<notin> dom f \<Longrightarrow> (extend x y f)`x = y"
  by (auto intro!: eval_eqI' set_right_unique_onI)

lemma extend_eval_eq' [simp]:
  "x \<noteq> y \<Longrightarrow> (extend y z f)`x = f`x"
  unfolding extend_def eval_def by (auto iff: mem_insert_iff)

lemma bin_union_eval_eq_left_eval [simp]:
  "x \<notin> dom g \<Longrightarrow> (f \<union> g)`x = f`x"
  unfolding eval_def by (cases "\<exists>y. \<langle>x, y\<rangle> \<in> g") auto

lemma bin_union_eval_eq_right_eval [simp]:
  "x \<notin> dom f \<Longrightarrow> (f \<union> g)`x = g`x"
  unfolding eval_def by (cases "\<exists>y. \<langle>x, y\<rangle> \<in> f") auto

lemma restriction_eval_eq [simp]:
  assumes "P x"
  shows "(f\<restriction>\<^bsub>P\<^esub>)`x = f`x"
  using assms unfolding eval_def set_restrict_left_pred_def by auto

lemma glue_eval_eqI:
  assumes "\<And>f f'. f \<in> F \<Longrightarrow> f' \<in> F \<Longrightarrow> set_right_unique_on {x} (glue {f, f'})"
  and "f \<in> F"
  and "x \<in> dom f"
  shows "(glue F)`x = f`x"
proof (rule eval_eqI[where ?P="mem_of {x}"], fold set_right_unique_on_set_def)
  from assms(1) show "set_right_unique_on {x} (glue F)"
    by (auto intro: set_right_unique_on_glueI)
  from assms(1)[OF assms(2) assms(2)] have "set_right_unique_on {x} f" by auto
  with assms(3) have "\<langle>x, f`x\<rangle> \<in> f"
    by (intro pair_eval_mem_if_mem_dom_if_set_right_unique_on)
  with assms(2) show "\<langle>x, f`x\<rangle> \<in> (glue F)" by auto
qed simp


subsubsection \<open>Dependent Functions\<close>

definition "dep_functions A B \<equiv>
  {f \<in> powerset (\<Sum>x \<in> A. B x) | set_left_total_on A f \<and> set_right_unique_on A f}"

abbreviation "functions A B \<equiv> dep_functions A (\<lambda>_. B)"

bundle hotg_functions_syntax
begin
syntax
  "_set_functions_telescope" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  (infixr "\<rightarrow>" 55)
end
bundle no_hotg_functions_syntax
begin
no_syntax
  "_set_functions_telescope" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  (infixr "\<rightarrow>" 55)
end
unbundle hotg_functions_syntax

translations
  "(x y \<in> A) \<rightarrow> B" \<rightharpoonup> "(x \<in> A)(y \<in> A) \<rightarrow> B"
  "(x \<in> A) args \<rightarrow> B" \<rightharpoonup> "(x \<in> A) \<rightarrow> args \<rightarrow> B"
  "(x \<in> A) \<rightarrow> B" \<rightleftharpoons> "CONST dep_functions A (\<lambda>x. B)"
  "A \<rightarrow> B" \<rightleftharpoons> "CONST functions A B"

lemma mem_dep_functionsI [intro]:
  assumes "f \<subseteq> (\<Sum>x \<in> A. (B x))"
  and "set_left_total_on A f"
  and "set_right_unique_on A f"
  shows "f \<in> (x \<in> A) \<rightarrow> (B x)"
  using assms unfolding dep_functions_def by auto

lemma mem_dep_functionsE [elim]:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)"
  obtains "f \<subseteq> \<Sum>x \<in> A. (B x)" "set_left_total_on A f" "set_right_unique_on A f"
  using assms unfolding dep_functions_def by blast

lemma dep_functions_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A' \<Longrightarrow> B x = B' x\<rbrakk> \<Longrightarrow> (x \<in> A) \<rightarrow> (B x) = (x \<in> A') \<rightarrow> (B' x)"
  unfolding dep_functions_def by simp

lemma mem_functions_if_mem_dep_functions:
  "f \<in> (x \<in> A) \<rightarrow> (B x) \<Longrightarrow> f \<in> (A \<rightarrow> (\<Union>x \<in> A. B x))"
  unfolding dep_functions_def by auto

lemma dom_eq_if_mem_dep_functions [simp]:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)"
  shows "dom f = A"
  using assms by (elim mem_dep_functionsE, intro eq_if_subset_if_subset) auto

lemma rng_subset_if_mem_dep_functions [simp]:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)"
  shows "rng f \<subseteq> (\<Union>x \<in> A. B x)"
proof -
  from assms have "f \<subseteq> \<Sum>x \<in> A. (B x)" by (elim mem_dep_functionsE)
  then have "rng f \<subseteq> rng (\<Sum>x \<in> A. (B x))" by blast
  also have "... \<subseteq> (\<Union>x \<in> A. B x)" by simp
  finally show ?thesis .
qed

lemma fst_snd_eq_pair_if_mem_dep_function [simp]:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)"
  and "p \<in> f"
  shows "\<langle>fst p, snd p\<rangle> = p"
  using assms by (auto elim!: mem_dep_functionsE)

lemma pair_eval_mem_if_mem_if_mem_dep_functions [elim]:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)"
  and "x \<in> A"
  shows "\<langle>x, f`x\<rangle> \<in> f"
proof -
  from assms have "x \<in> dom f" by simp
  then show ?thesis using assms
    by (elim mem_dep_functionsE mem_domE, intro pair_eval_mem_if_ex1_pair_mem)
    (auto dest: set_right_unique_onD)
qed

lemma pair_mem_iff_eval_eq_if_mem_dom_dep_function:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)"
  and "x \<in> A"
  shows "\<langle>x, y\<rangle> \<in> f \<longleftrightarrow> f`x = y"
proof
  assume "\<langle>x, y\<rangle> \<in> f"
  moreover have "\<langle>x, f`x\<rangle> \<in> f" using assms by auto
  ultimately show "f`x = y" using assms
    by (auto dest: set_right_unique_onD)
qed (insert assms, auto)

lemma fst_mem_if_mem_dep_function:
  "\<lbrakk>f \<in> (x \<in> A) \<rightarrow> (B x); p \<in> f\<rbrakk> \<Longrightarrow> fst p \<in> A"
  by (auto elim!: mem_dep_functionsE)

lemma snd_mem_if_mem_dep_function:
  "\<lbrakk>f \<in> (x \<in> A) \<rightarrow> (B x); p \<in> f\<rbrakk> \<Longrightarrow> snd p \<in> B (fst p)"
  by (auto elim!: mem_dep_functionsE)

lemma mem_dom_if_pair_mem_dep_function:
  "\<lbrakk>f \<in> (x \<in> A) \<rightarrow> (B x); \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> x \<in> A"
  using fst_mem_if_mem_dep_function[where ?p="\<langle>x, y\<rangle>"] by auto

lemma mem_codom_if_pair_mem_dep_function:
  "\<lbrakk>f \<in> (x \<in> A) \<rightarrow> (B x); \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> y \<in> B x"
  using snd_mem_if_mem_dep_function[where ?p="\<langle>x, y\<rangle>"] by auto

lemma eval_mem_if_mem_if_mem_dep_functions [elim]:
  "\<lbrakk>f \<in> (x \<in> A) \<rightarrow> (B x); x \<in> A\<rbrakk> \<Longrightarrow> f`x \<in> B x"
  using mem_codom_if_pair_mem_dep_function
  by (blast dest: pair_eval_mem_if_mem_if_mem_dep_functions)

lemma eval_eq_if_pair_mem_dep_function [simp]:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)"
  and "\<langle>x, y\<rangle> \<in> f"
  shows "f`x = y"
  using assms fst_mem_if_mem_dep_function[OF assms]
    by (auto iff: pair_mem_iff_eval_eq_if_mem_dom_dep_function)

lemma mem_dom_dep_functionE:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)"
  and "x \<in> A"
  obtains y where "f`x = y" "y \<in> B x"
  using assms eval_mem_if_mem_if_mem_dep_functions by auto

lemma mem_dep_functionE [elim]:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)"
  and "p \<in> f"
  obtains x y where "p = \<langle>x, y\<rangle>" "x \<in> A" "y \<in> B x" "f`x = y"
proof -
  assume hyp: "\<And>x y. p = \<langle>x, y\<rangle> \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> B x \<Longrightarrow> f`x = y \<Longrightarrow> thesis"
  obtain x y where [simp]: "p = \<langle>x, y\<rangle>" using assms
    by (auto elim!: mem_dep_functionsE)
  show thesis
  proof (intro hyp[of x y])
    from fst_mem_if_mem_dep_function[OF assms] show "x \<in> A" by simp
    from snd_mem_if_mem_dep_function[OF assms] show "y \<in> B x" by simp
    from assms show "f`x = y" by auto
  qed fact
qed

lemma repl_eval_eq_dep_function [simp]:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)"
  shows "{\<langle>x, f`x\<rangle> | x \<in> A} = f"
  using assms by (intro eqI) auto

text \<open>Note: functions are not contravariant on their domain.\<close>
lemma mem_dep_functions_covariant_codom:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)"
  and "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> B x \<Longrightarrow> f`x \<in> B' x"
  shows "f \<in> (x \<in> A) \<rightarrow> (B' x)"
  by (rule mem_dep_functionsE[OF assms(1)], intro mem_dep_functionsI)
    (insert assms, auto)

corollary mem_dep_functions_covariant_codom_subset:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)"
  and "\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> B' x"
  shows "f \<in> (x \<in> A) \<rightarrow> (B' x)"
  using assms(2) by (intro mem_dep_functions_covariant_codom[OF assms(1)]) auto

lemma eq_if_mem_if_mem_agree_if_mem_dep_functions:
  assumes mem_dep_functions: "\<And>f. f \<in> F \<Longrightarrow> \<exists>B. f \<in> (x \<in> A) \<rightarrow> (B x)"
  and "agree A F"
  and "f \<in> F"
  and "g \<in> F"
  shows "f = g"
  using assms
proof -
  have "\<And>f. f \<in> F \<Longrightarrow> \<exists>B. f \<subseteq> \<Sum>x \<in> A. (B x)" by (blast dest: mem_dep_functions)
  with assms show ?thesis by (intro eq_if_subset_dep_pairs_if_agree)
qed

lemma subset_if_agree_if_mem_dep_functions:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)"
  and "f \<in> F"
  and "agree A F"
  and "g \<in> F"
  shows "f \<subseteq> g"
  using assms
  by (elim mem_dep_functionsE subset_if_agree_if_subset_dep_pairs) auto

lemma agree_if_eval_eq_if_mem_dep_functions:
  assumes mem_dep_functions: "\<And>f. f \<in> F \<Longrightarrow> \<exists>B. f \<in> (x \<in> A) \<rightarrow> (B x)"
  and "\<And>f g x. f \<in> F \<Longrightarrow> g \<in> F \<Longrightarrow> x \<in> A \<Longrightarrow> f`x = g`x"
  shows "agree A F"
proof (subst agree_set_iff_agree, rule agreeI)
  fix x y f g assume hyps: "f \<in> F" "g \<in> F" "x \<in> A" and "\<langle>x, y\<rangle> \<in> f"
  then have "y = f`x" using assms(1) by auto
  also have "... = g`x" by (fact assms(2)[OF hyps])
  finally have y_eq: "y = g`x" .
  from assms(1)[OF \<open>g \<in> F\<close>] obtain B where "g \<in> (x \<in> A) \<rightarrow> (B x)" by blast
  with y_eq pair_mem_iff_eval_eq_if_mem_dom_dep_function \<open>x \<in> A\<close>
    show "\<langle>x, y\<rangle> \<in> g" by blast
qed

lemma eq_if_agree_if_mem_dep_functions:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)" "g \<in> (x \<in> A) \<rightarrow> (B x)"
  and "agree A {f, g}"
  shows "f = g"
  using assms
  by (intro eq_if_mem_if_mem_agree_if_mem_dep_functions[of "{f, g}"]) auto

lemma dep_functions_ext:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)" "g \<in> (x \<in> A) \<rightarrow> (B x)"
  and "\<And>x. x \<in> A \<Longrightarrow> f`x = g`x"
  shows "f = g"
  using assms
  by (intro eq_if_agree_if_mem_dep_functions)
    (auto intro:
      agree_if_eval_eq_if_mem_dep_functions[unfolded agree_set_iff_agree])

lemma dep_functions_eval_eqI:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)" "g \<in> (x \<in> A') \<rightarrow> (B' x)"
  and "f \<subseteq> g"
  and "x \<in> A \<inter> A'"
  shows "f`x = g`x"
proof -
  from assms have "\<langle>x, f`x\<rangle> \<in> g" and "\<langle>x, g`x\<rangle> \<in> g" by auto
  then show ?thesis using assms by auto
qed

lemma dep_functions_eq_if_subset:
  assumes f_mem: "f \<in> (x \<in> A) \<rightarrow> (B x)"
  and g_mem: "g \<in> (x \<in> A) \<rightarrow> (B' x)"
  and "f \<subseteq> g"
  shows "f = g"
proof (rule eqI)
  fix p assume "p \<in> g"
  with g_mem obtain x y where [simp]: "p = \<langle>x, y\<rangle>" "g`x = y" "x \<in> A" by auto
  with assms have [simp]: "f`x = g`x" by (intro dep_functions_eval_eqI) auto
  show "p \<in> f" using f_mem
    by (auto iff: pair_mem_iff_eval_eq_if_mem_dom_dep_function)
qed (insert assms, auto)

lemma ex_dom_mem_dep_functions_iff:
  "(\<exists>A. f \<in> (x \<in> A) \<rightarrow> (B x)) \<longleftrightarrow> f \<in> (x \<in> dom f) \<rightarrow> (B x)"
  by auto

lemma mem_dep_functions_empty_dom_iff_eq_empty [iff]:
  "(f \<in> (x \<in> {}) \<rightarrow> (B x)) \<longleftrightarrow> f = {}"
  by auto

lemma empty_mem_dep_functions: "{} \<in> (x \<in> {}) \<rightarrow> (B x)" by simp

lemma eq_singleton_if_mem_functions_singleton [simp]:
  "f \<in> {a} \<rightarrow> {b} \<Longrightarrow> f = {\<langle>a, b\<rangle>}"
  by auto

lemma singleton_mem_functionsI [intro]: "y \<in> B \<Longrightarrow> {\<langle>x, y\<rangle>} \<in> {x} \<rightarrow> B"
  by auto

lemma mem_dep_functions_collectI:
  assumes f_mem: "f \<in> (x \<in> A) \<rightarrow> (B x)"
  and "\<And>x. x \<in> A \<Longrightarrow> P x (f`x)"
  shows "f \<in> (x \<in> A) \<rightarrow> {y \<in> B x | P x y}"
  by (rule mem_dep_functions_covariant_codom) (insert assms, auto)

lemma mem_dep_functions_collectD:
  assumes "f \<in> (x \<in> A) \<rightarrow> {y \<in> B x | P x y}"
  shows "f \<in> (x \<in> A) \<rightarrow> (B x)" and "\<And>x. x \<in> A \<Longrightarrow> P x (f`x)"
proof -
  from assms show "f \<in> (x \<in> A) \<rightarrow> (B x)"
    by (rule mem_dep_functions_covariant_codom_subset) auto
  fix x assume "x \<in> A"
  with assms show "P x (f`x)"
    by (auto dest: pair_eval_mem_if_mem_if_mem_dep_functions)
qed


end