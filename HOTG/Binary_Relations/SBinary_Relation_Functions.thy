\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Functions on Relations\<close>
theory SBinary_Relation_Functions
  imports
    Pairs
    Replacement_Predicates
begin

subsubsection \<open>Inverse\<close>

(*TODO: replace condition with a new is_pair predicate*)
definition "set_rel_inv R \<equiv> {\<langle>y, x\<rangle> | \<langle>x, y\<rangle> \<in> {p \<in> R | \<exists>x y. p = \<langle>x, y\<rangle>}}"

bundle hotg_rel_inv_syntax
begin
notation set_rel_inv ("(_\<inverse>)" [1000])
end
bundle no_hotg_rel_inv_syntax
begin
no_notation set_rel_inv ("(_\<inverse>)" [1000])
end

unbundle no_rel_inv_syntax
unbundle hotg_rel_inv_syntax

lemma mem_set_rel_invI [intro]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  shows "\<langle>y, x\<rangle> \<in> R\<inverse>"
  using assms unfolding set_rel_inv_def by auto

lemma mem_set_rel_invE [elim!]:
  assumes "p \<in> R\<inverse>"
  obtains x y where "p = \<langle>y, x\<rangle>" "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding set_rel_inv_def uncurry_def by (auto)

lemma set_rel_inv_pairs_eq [simp]: "(A \<times> B)\<inverse> = B \<times> A"
  by auto

lemma set_rel_inv_empty_eq [simp]: "{}\<inverse> = {}"
  by auto

lemma set_rel_inv_inv_eq: "R\<inverse>\<inverse> = {p \<in> R | \<exists>x y. p = \<langle>x, y\<rangle>}"
  by auto

lemma mono_set_rel_inv: "mono set_rel_inv"
  by (intro monoI) auto


subsubsection \<open>Extensions and Restricts\<close>

definition "extend x y R \<equiv> insert \<langle>x, y\<rangle> R"

lemma mem_extendI [intro]: "\<langle>x, y\<rangle> \<in> extend x y R"
  unfolding extend_def by blast

lemma mem_extendI':
  assumes "p \<in> R"
  shows "p \<in> extend x y R"
  unfolding extend_def using assms by blast

lemma mem_extendE [elim]:
  assumes "p \<in> extend x y R"
  obtains "p = \<langle>x, y\<rangle>" | "p \<noteq> \<langle>x, y\<rangle>" "p \<in> R"
  using assms unfolding extend_def by blast

lemma extend_eq_self_if_pair_mem [simp]: "\<langle>x, y\<rangle> \<in> R \<Longrightarrow> extend x y R = R"
  by (auto intro: mem_extendI')

lemma insert_pair_eq_extend: "insert \<langle>x, y\<rangle> R = extend x y R"
  by (auto intro: mem_extendI')

lemma mono_extend_set: "mono (extend x y)"
  by (intro monoI) (auto intro: mem_extendI')


definition "glue \<R> \<equiv> \<Union>\<R>"

lemma mem_glueI [intro]:
  assumes "p \<in> R"
  and "R \<in> \<R>"
  shows "p \<in> glue \<R>"
  using assms unfolding glue_def by blast

lemma mem_glueE [elim!]:
  assumes "p \<in> glue \<R>"
  obtains R where "p \<in> R" "R \<in> \<R>"
  using assms unfolding glue_def by blast

lemma glue_empty_eq [simp]: "glue {} = {}" by auto

lemma glue_singleton_eq [simp]: "glue {R} = R" by auto

lemma mono_glue: "mono glue"
  by (intro monoI) auto


consts set_restrict_left :: "set \<Rightarrow> 'a \<Rightarrow> set"

definition "set_restrict_right R P \<equiv> (set_restrict_left R\<inverse> P)\<inverse>"

bundle hotg_restrict_syntax
begin
notation set_restrict_left ("(_)\<restriction>(\<^bsub>_\<^esub>)" [1000])
notation set_restrict_right ("(_)\<upharpoonleft>(\<^bsub>_\<^esub>)" [1000])
end
bundle no_hotg_restrict_syntax
begin
no_notation set_restrict_left ("(_)\<restriction>(\<^bsub>_\<^esub>)" [1000])
no_notation set_restrict_right ("(_)\<upharpoonleft>(\<^bsub>_\<^esub>)" [1000])
end
unbundle no_restrict_syntax
unbundle hotg_restrict_syntax

overloading
  set_restrict_left_pred \<equiv> "set_restrict_left :: set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set"
  set_restrict_left_set \<equiv> "set_restrict_left :: set \<Rightarrow> set \<Rightarrow> set"
begin
  definition "set_restrict_left_pred R P \<equiv> {p \<in> R | \<exists>x y. P x \<and> p = \<langle>x, y\<rangle>}"
  definition "set_restrict_left_set R A \<equiv> set_restrict_left R (mem_of A)"
end

lemma set_restrict_left_set_eq_set_restrict_left [simp]:
  "R\<restriction>\<^bsub>A\<^esub> = R\<restriction>\<^bsub>mem_of A\<^esub>"
  unfolding set_restrict_left_set_def by simp

lemma mem_set_restrict_leftI [intro!]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  and "P x"
  shows "\<langle>x, y\<rangle> \<in> R\<restriction>\<^bsub>P\<^esub>"
  using assms unfolding set_restrict_left_pred_def by blast

lemma mem_set_restrict_leftE [elim]:
  assumes "p \<in> R\<restriction>\<^bsub>P\<^esub>"
  obtains x y where "p = \<langle>x, y\<rangle>" "P x" "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding set_restrict_left_pred_def by blast

lemma mem_set_restrict_rightI [intro!]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  and "P y"
  shows "\<langle>x, y\<rangle> \<in> R\<upharpoonleft>\<^bsub>P\<^esub>"
  using assms unfolding set_restrict_right_def by blast

lemma mem_set_restrict_rightE [elim]:
  assumes "p \<in> R\<upharpoonleft>\<^bsub>P\<^esub>"
  obtains x y where "p = \<langle>x, y\<rangle>" "P y" "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding set_restrict_right_def by blast

lemma set_restrict_left_empty_eq [simp]: "{}\<restriction>\<^bsub>P :: set \<Rightarrow> bool\<^esub> = {}" by auto

lemma set_restrict_left_empty_eq' [simp]: "R\<restriction>\<^bsub>{}\<^esub> = {}" by auto

lemma set_restrict_left_subset_self [iff]: "R\<restriction>\<^bsub>P :: set \<Rightarrow> bool\<^esub> \<subseteq> R" by auto

lemma set_restrict_left_dep_pairs_eq_dep_pairs_collect [simp]:
  "(\<Sum>x \<in> A. B x)\<restriction>\<^bsub>P\<^esub> = (\<Sum>x \<in> {a \<in> A | P a}. B x)"
  by auto

lemma set_restrict_left_dep_pairs_eq_dep_pairs_bin_inter [simp]:
  "(\<Sum>x \<in> A. B x)\<restriction>\<^bsub>A'\<^esub> = (\<Sum>x \<in> A \<inter> A'. B x)"
  by simp

lemma set_restrict_left_subset_dep_pairs_if_subset_dep_pairs [intro]:
  assumes "R \<subseteq> \<Sum>x \<in> A. B x"
  shows "R\<restriction>\<^bsub>P\<^esub> \<subseteq> \<Sum>x \<in> {x \<in> A | P x}. B x"
  using assms by auto

lemma set_restrict_left_set_restrict_left_eq_set_restrict_left [simp]:
  fixes P P' :: "set \<Rightarrow> bool"
  shows "(R\<restriction>\<^bsub>P\<^esub>)\<restriction>\<^bsub>P\<^esub> = R\<restriction>\<^bsub>P\<^esub>"
  by auto

lemma mono_set_restrict_left_set: "mono (\<lambda>R. R\<restriction>\<^bsub>P :: set \<Rightarrow> bool\<^esub>)"
  by (intro monoI) auto

lemma mono_set_restrict_left_pred: "mono (\<lambda>P. R\<restriction>\<^bsub>P :: set \<Rightarrow> bool\<^esub>)"
  by (intro monoI) auto


definition "agree P \<R> \<equiv> \<forall>R R' \<in> \<R>. R\<restriction>\<^bsub>P\<^esub> = R'\<restriction>\<^bsub>P\<^esub>"

lemma agree_set_iff_agree [iff]: "agree A \<R> \<longleftrightarrow> agree (mem_of A) \<R>"
  unfolding agree_def by simp

lemma agreeI [intro]:
  assumes "\<And>x y R R'. P x \<Longrightarrow> R \<in> \<R> \<Longrightarrow> R' \<in> \<R> \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<Longrightarrow> \<langle>x, y\<rangle> \<in> R'"
  shows "agree P \<R>"
  using assms unfolding agree_def by blast

lemma agreeD:
  assumes "agree P \<R>"
  and "P x"
  and "R \<in> \<R>" "R' \<in> \<R>"
  and "\<langle>x, y\<rangle> \<in> R"
  shows "\<langle>x, y\<rangle> \<in> R'"
proof -
  from assms(2, 5) have "\<langle>x, y\<rangle> \<in> R\<restriction>\<^bsub>P\<^esub>" by (intro mem_set_restrict_leftI)
  moreover from assms(1, 3-4) have "... = R'\<restriction>\<^bsub>P\<^esub>" unfolding agree_def by blast
  ultimately show ?thesis by auto
qed

lemma antimono_agree_pred: "antimono (\<lambda>P. agree (P :: set \<Rightarrow> bool) \<R>)"
  by (intro antimonoI) (auto dest: agreeD)

lemma antimono_agree_set: "antimono (\<lambda>\<R>. agree (P :: set \<Rightarrow> bool) \<R>)"
  by (intro antimonoI) (auto dest: agreeD)

lemma set_restrict_left_eq_set_restrict_left_if_agree:
  fixes P :: "set \<Rightarrow> bool"
  assumes "agree P \<R>"
  and "R \<in> \<R>" "R' \<in> \<R>"
  shows "R\<restriction>\<^bsub>P\<^esub> = R'\<restriction>\<^bsub>P\<^esub>"
  using assms by (auto dest: agreeD)

lemma eq_if_subset_dep_pairs_if_agree:
  assumes "agree A \<R>"
  and subset_dep_pairs: "\<And>R. R \<in> \<R> \<Longrightarrow> \<exists>B. R \<subseteq> \<Sum>x \<in> A. B x"
  and "R \<in> \<R>"
  and "R' \<in> \<R>"
  shows "R = R'"
proof -
  from subset_dep_pairs[OF \<open>R \<in> \<R>\<close>] have "R = R\<restriction>\<^bsub>A\<^esub>" by auto
  also with assms have "... = R'\<restriction>\<^bsub>A\<^esub>"
    by ((subst set_restrict_left_set_eq_set_restrict_left)+,
      intro set_restrict_left_eq_set_restrict_left_if_agree)
    auto
  also from subset_dep_pairs[OF \<open>R' \<in> \<R>\<close>] have "... = R'" by auto
  finally show ?thesis .
qed

lemma subset_if_agree_if_subset_dep_pairs:
  assumes subset_dep_pairs: "R \<subseteq> \<Sum>x \<in> A. B x"
  and "R \<in> \<R>"
  and "agree A \<R>"
  and "R' \<in> \<R>"
  shows "R \<subseteq> R'"
  using assms by (auto simp: agreeD[where ?R="R"])


subsubsection \<open>Domain and Range\<close>

definition "dom R \<equiv> {x | p \<in> R, \<exists>y. p = \<langle>x, y\<rangle>}"

lemma mem_domI [intro]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  shows "x \<in> dom R"
  using assms unfolding dom_def by fast

lemma mem_domE [elim!]:
  assumes "x \<in> dom R"
  obtains y where "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding dom_def by blast

lemma mono_dom: "mono dom"
  by (intro monoI) auto

lemma dom_empty_eq [simp]: "dom {} = {}"
  by auto

lemma dom_union_eq [simp]: "dom (\<Union>\<R>) = \<Union>{dom R | R \<in> \<R>}"
  by auto

lemma dom_bin_union_eq [simp]: "dom (R \<union> S) = dom R \<union> dom S"
  by auto

lemma dom_collect_eq [simp]: "dom {\<langle>f x, g x\<rangle> | x \<in> A} = {f x | x \<in> A}"
  by auto

lemma dom_extend_eq [simp]: "dom (extend x y R) = insert x (dom R)"
  by (rule eqI) (auto intro: mem_extendI')

lemma dom_dep_pairs_eqI [intro]:
  assumes "\<And>x. B x \<noteq> {}"
  shows "dom (\<Sum>x \<in> A. B x) = A"
  using assms by (intro eqI) auto

lemma dom_restrict_left_eq [simp]: "dom (R\<restriction>\<^bsub>P\<^esub>) = {x \<in> dom R | P x}"
  by auto

lemma dom_restrict_left_set_eq [simp]: "dom (R\<restriction>\<^bsub>A\<^esub>) = dom R \<inter> A" by simp

lemma glue_subset_dep_pairsI:
  fixes \<R> defines "D \<equiv> \<Union>R \<in> \<R>. dom R"
  assumes all_subset_dep_pairs: "\<And>R. R \<in> \<R> \<Longrightarrow> \<exists>A. R \<subseteq> \<Sum>x \<in> A. B x"
  shows "glue \<R> \<subseteq> \<Sum>x \<in> D. (B x)"
proof
  fix p assume "p \<in> glue \<R>"
  with all_subset_dep_pairs obtain R A where "p \<in> R" "R \<in> \<R>" "R \<subseteq> \<Sum>x \<in> A. B x"
    by blast
  then obtain x y where "p = \<langle>x, y\<rangle>" "x \<in> dom R" "y \<in> B x" by blast
  with \<open>R \<in> \<R>\<close> have "x \<in> D" unfolding D_def by auto
  with \<open>p = \<langle>x, y\<rangle>\<close> \<open>y \<in> B x\<close> show "p \<in> \<Sum>x \<in> D. (B x)" by auto
qed

definition "rng R \<equiv> {y | p \<in> R, \<exists>x. p = \<langle>x, y\<rangle>}"

lemma mem_rngI [intro]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  shows "y \<in> rng R"
  using assms unfolding rng_def by fast

lemma mem_rngE [elim!]:
  assumes "y \<in> rng R"
  obtains x where "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding rng_def by blast

lemma mono_rng: "mono rng"
  by (intro monoI) auto

lemma rng_empty_eq [simp]: "rng {} = {}"
  by auto

lemma rng_union_eq [simp]: "rng (\<Union>\<R>) = \<Union>{rng R | R \<in> \<R>}"
  by auto

lemma rng_bin_union_eq [simp]: "rng (R \<union> S) = rng R \<union> rng S"
  by auto

lemma rng_collect_eq [simp]: "rng {\<langle>f x, g x\<rangle> | x \<in> A} = {g x | x \<in> A}"
  by auto

lemma rng_extend_eq [simp]: "rng (extend x y R) = insert y (rng R)"
  by (rule eqI) (auto intro: mem_extendI')

lemma rng_dep_pairs_eq [simp]: "rng (\<Sum>x \<in> A. B x) = (\<Union>x \<in> A. B x)"
  by auto

lemma dom_rel_inv_eq_rng [simp]: "dom R\<inverse> = rng R"
  by auto

lemma rng_rel_inv_eq_dom [simp]: "rng R\<inverse> = dom R"
  by auto


subsubsection \<open>Composition\<close>

definition "set_comp S R \<equiv>
  {p \<in> dom R \<times> rng S | \<exists>z. \<langle>fst p, z\<rangle> \<in> R \<and> \<langle>z, snd p\<rangle> \<in> S}"

bundle hotg_comp_syntax begin notation set_comp (infixr "\<circ>" 60) end
bundle no_hotg_comp_syntax begin no_notation set_comp (infixr "\<circ>" 60) end
unbundle no_comp_syntax
unbundle hotg_comp_syntax

lemma mem_compI [intro!]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  and "\<langle>y, z\<rangle> \<in> S"
  shows "\<langle>x, z\<rangle> \<in> S \<circ> R"
  using assms unfolding set_comp_def by auto

lemma mem_compE [elim!]:
  assumes "p \<in> S \<circ> R"
  obtains x y z where "\<langle>x, y\<rangle> \<in> R" "\<langle>y, z\<rangle> \<in> S" "p = \<langle>x, z\<rangle>"
  using assms unfolding set_comp_def by auto

lemma dep_pairs_comp_pairs_eq:
  "((\<Sum>x \<in> B. (C x)) \<circ> (A \<times> B)) = A \<times> (\<Union>x \<in> B. (C x))"
  by auto

lemma set_comp_assoc: "T \<circ> S \<circ> R = (T \<circ> S) \<circ> R"
  by auto

lemma mono_set_comp_left: "mono (\<lambda>R. R \<circ> S)"
  by (intro monoI) auto

lemma mono_set_comp_right: "mono (\<lambda>S. R \<circ> S)"
  by (intro monoI) auto


subsubsection \<open>Diagonal\<close>

definition "diag A \<equiv> {\<langle>a, a\<rangle> | a \<in> A}"

lemma mem_diagI [intro!]: "a \<in> A \<Longrightarrow> \<langle>a, a\<rangle> \<in> diag A"
  unfolding diag_def by auto

lemma mem_diagE [elim!]:
  assumes "p \<in> diag A"
  obtains a where "a \<in> A" "p = \<langle>a, a\<rangle>"
  using assms unfolding diag_def by auto

lemma mono_diag: "mono diag"
  by (intro monoI) auto


end