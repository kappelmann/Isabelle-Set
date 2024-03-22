\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Functions on Relations\<close>
theory SBinary_Relation_Functions
  imports
    Pairs
    Replacement_Predicates
    Transport.Binary_Relation_Functions
begin

unbundle no_HOL_ascii_syntax

definition "rel R x y \<equiv> \<langle>x, y\<rangle> \<in> R"

lemma rel_of_eq: "rel = (\<lambda>R x y. \<langle>x, y\<rangle> \<in> R)" unfolding rel_def by simp
lemma rel_of_iff [iff]: "rel R x y \<longleftrightarrow> \<langle>x, y\<rangle> \<in> R" unfolding rel_def by simp
declare rel_of_iff[symmetric, set_to_HOL_simp]

subsubsection \<open>Domain, Codomain, and Field\<close>

definition "dom R \<equiv> {x | p \<in> R, \<exists>y. p = \<langle>x, y\<rangle>}"

lemma mem_domI [intro]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  shows "x \<in> dom R"
  using assms unfolding dom_def by fast

lemma mem_domE [elim!]:
  assumes "x \<in> dom R"
  obtains y where "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding dom_def by blast

lemma mono_subset_dom: "((\<subseteq>) \<Rrightarrow>\<^sub>m (\<subseteq>)) dom"
  by auto

lemma dom_empty_eq [simp]: "dom {} = {}"
  by auto

lemma dom_union_eq [simp]: "dom (\<Union>\<R>) = \<Union>{dom R | R \<in> \<R>}"
  by auto

lemma dom_bin_union_eq [simp]: "dom (R \<union> S) = dom R \<union> dom S"
  by auto

lemma dom_collect_eq [simp]: "dom {\<langle>f x, g x\<rangle> | x \<in> A} = {f x | x \<in> A}"
  by auto

lemma dom_dep_pairs_eqI [intro]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> B x \<noteq> {}"
  shows "dom (\<Sum>x \<in> A. B x) = A"
  using assms by (intro eqI') auto

lemma mem_of_dom_eq_in_dom_rel [simp, set_to_HOL_simp]: "mem_of (dom R) = in_dom (rel R)"
  by (intro ext) auto


definition "codom R \<equiv> {y | p \<in> R, \<exists>x. p = \<langle>x, y\<rangle>}"

lemma mem_codomI [intro]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  shows "y \<in> codom R"
  using assms unfolding codom_def by fast

lemma mem_codomE [elim!]:
  assumes "y \<in> codom R"
  obtains x where "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding codom_def by blast

lemma mono_subset_codom: "((\<subseteq>) \<Rrightarrow>\<^sub>m (\<subseteq>)) codom"
  by auto

lemma codom_empty_eq [simp]: "codom {} = {}"
  by auto

lemma codom_union_eq [simp]: "codom (\<Union>\<R>) = \<Union>{codom R | R \<in> \<R>}"
  by auto

lemma codom_bin_union_eq [simp]: "codom (R \<union> S) = codom R \<union> codom S"
  by auto

lemma codom_collect_eq [simp]: "codom {\<langle>f x, g x\<rangle> | x \<in> A} = {g x | x \<in> A}"
  by auto

lemma codom_dep_pairs_eq [simp]: "codom (\<Sum>x \<in> A. B x) = (\<Union>x \<in> A. B x)"
  by auto

lemma mem_of_codom_eq_in_codom_rel [simp, set_to_HOL_simp]: "mem_of (codom R) = in_codom (rel R)"
  by (intro ext) auto


definition "field R \<equiv> dom R \<union> codom R"

lemma field_eq_dom_bin_union_codom: "field R = dom R \<union> codom R"
  unfolding field_def by auto

lemma mem_field_iff_mem_dom_or_codom [iff]: "x \<in> field R \<longleftrightarrow> x \<in> dom R \<or> x \<in> codom R"
  unfolding field_def by auto

lemma field_union_eq [simp]: "field (\<Union>\<R>) = \<Union>{field R | R \<in> \<R>}"
  by blast

lemma field_bin_union_eq [simp]: "field (R \<union> S) = field R \<union> field S"
  by auto

lemma field_collect_eq [simp]: "field {\<langle>f x, g x\<rangle> | x \<in> A} = ({f x | x \<in> A} \<union> {g x | x \<in> A})"
  by blast

lemma mem_of_field_eq_in_field_rel [simp, set_to_HOL_simp]: "mem_of (field R) = in_field (rel R)"
  by (intro ext) auto


subsubsection \<open>Composition\<close>

definition "set_rel_comp R S \<equiv> {p \<in> dom R \<times> codom S | \<exists>z. \<langle>fst p, z\<rangle> \<in> R \<and> \<langle>z, snd p\<rangle> \<in> S}"

bundle hotg_rel_comp_syntax begin notation set_rel_comp (infixl "\<circ>\<circ>" 55) end
bundle no_hotg_set_rel_comp_syntax begin no_notation set_rel_comp (infixl "\<circ>\<circ>" 55) end
unbundle
  no_rel_comp_syntax
  hotg_rel_comp_syntax

lemma mem_rel_compI:
  assumes "is_pair p"
  assumes "\<langle>fst p, y\<rangle> \<in> R"
  and "\<langle>y, snd p\<rangle> \<in> S"
  shows "p \<in> R \<circ>\<circ> S"
  using assms unfolding set_rel_comp_def by force

lemma pair_mem_rel_compI [intro]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  and "\<langle>y, z\<rangle> \<in> S"
  shows "\<langle>x, z\<rangle> \<in> R \<circ>\<circ> S"
  using assms by (auto intro: mem_rel_compI)

lemma mem_rel_compE [elim]:
  assumes "p \<in> R \<circ>\<circ> S"
  obtains x y z where "\<langle>x, y\<rangle> \<in> R" "\<langle>y, z\<rangle> \<in> S" "p = \<langle>x, z\<rangle>"
  using assms unfolding set_rel_comp_def by auto

lemma rel_rel_comp_eq_rel_comp_rel [simp, set_to_HOL_simp]: "rel (R \<circ>\<circ> S) = rel_comp (rel R) (rel S)"
  by (intro ext) auto

lemma dep_pairs_comp_pairs_eq:
  "((A \<times> B) \<circ>\<circ> (\<Sum>x \<in> B. (C x))) = A \<times> (\<Union>x \<in> B. (C x))"
  by auto

lemma set_rel_comp_assoc: "R \<circ>\<circ> (S \<circ>\<circ> T) = (R \<circ>\<circ> S) \<circ>\<circ> T"
  by force

lemma mono_subset_set_rel_comp: "((\<subseteq>) \<Rrightarrow>\<^sub>m (\<subseteq>) \<Rrightarrow> (\<subseteq>)) (\<circ>\<circ>)"
  by (intro dep_mono_wrt_relI Dep_Fun_Rel_relI) blast

lemma dom_rel_comp_subset_dom: "dom (R \<circ>\<circ> S) \<subseteq> dom R"
  by auto

lemma codom_rel_comp_subset_codom: "codom (R \<circ>\<circ> S) \<subseteq> codom S"
  by auto

lemma field_rel_comp_subset_dom_bin_union_codom: "field (R \<circ>\<circ> S) \<subseteq> dom R \<union> codom S"
  by auto

subsubsection \<open>Inverse\<close>

definition "set_rel_inv R \<equiv> {swap p | p \<in> {p \<in> R | is_pair p}}"

bundle hotg_rel_inv_syntax
begin
notation set_rel_inv ("(_\<inverse>)" [1000])
end
bundle no_hotg_rel_inv_syntax
begin
no_notation set_rel_inv ("(_\<inverse>)" [1000])
end
unbundle
  no_rel_inv_syntax
  hotg_rel_inv_syntax

lemma mem_rel_invI:
  assumes "is_pair p"
  assumes "\<langle>snd p, fst p\<rangle> \<in> R"
  shows "p \<in> R\<inverse>"
  using assms unfolding set_rel_inv_def by auto

lemma pair_mem_rel_invI [intro]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  shows "\<langle>y, x\<rangle> \<in> R\<inverse>"
  using assms by (auto intro: mem_rel_invI)

lemma mem_rel_invE [elim!]:
  assumes "p \<in> R\<inverse>"
  obtains x y where "p = \<langle>y, x\<rangle>" "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding set_rel_inv_def uncurry_def by (auto)

lemma set_rel_inv_pairs_eq [simp]: "(A \<times> B)\<inverse> = B \<times> A"
  by auto

lemma set_rel_inv_empty_eq [simp]: "{}\<inverse> = {}"
  by auto

lemma set_rel_inv_inv_eq: "R\<inverse>\<inverse> = {p \<in> R | is_pair p}"
  by force

lemma mono_subset_set_rel_inv: "((\<subseteq>) \<Rrightarrow>\<^sub>m (\<subseteq>)) set_rel_inv"
  by auto

lemma dom_rel_inv_eq_codom [simp]: "dom (R\<inverse>) = codom R"
  by (intro eqI') blast

lemma codom_rel_inv_eq_dom [simp]: "codom (R\<inverse>) = dom R"
  by (intro eqI') blast

lemma field_rel_inv_eq [simp]: "field R\<inverse> = field R"
  by (intro eqI') auto

lemma mem_rel_inv_iff_mem [simp]: "\<langle>x, y\<rangle> \<in> R\<inverse> \<longleftrightarrow> \<langle>y, x\<rangle> \<in> R"
  by blast

lemma rel_inv_comp_eq [simp]: "(R \<circ>\<circ> S)\<inverse> = S\<inverse> \<circ>\<circ> R\<inverse>"
  by (intro eqI') blast

lemma rel_rel_inv_eq_rel_inv_rel [simp, set_to_HOL_simp]: "rel (R\<inverse>) = rel_inv (rel R)"
  by auto


subsubsection \<open>Extensions\<close>

definition "extend x y R \<equiv> insert \<langle>x, y\<rangle> R"

lemma mem_extendI [intro]: "p = \<langle>x, y\<rangle> \<Longrightarrow> p \<in> extend x y R"
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

lemma mono_subset_extend_set: "((\<subseteq>) \<Rrightarrow>\<^sub>m (\<subseteq>)) (extend x y)"
  by (auto intro: mem_extendI')

lemma dom_extend_eq [simp]: "dom (extend x y R) = insert x (dom R)"
  by (rule eqI) (auto intro: mem_extendI')

lemma codom_extend_eq [simp]: "codom (extend x y R) = insert y (codom R)"
  by (rule eqI) (auto intro: mem_extendI')

lemma field_extend_eq [simp]: "field (extend x y R) = insert x (insert y (field R))"
  by (rule eqI) (auto intro: mem_extendI')


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

lemma glue_insert_eq [simp]: "glue (insert A \<R>) = A \<union> glue \<R>" by auto

lemma glue_bin_union_eq [simp]: "glue (A \<union> B) = glue A \<union> glue B" by auto

lemma mono_subset_glue: "((\<subseteq>) \<Rrightarrow>\<^sub>m (\<subseteq>)) glue"
  by auto

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


subsubsection \<open>Restrictions\<close>

overloading
  rel_restrict_left_set \<equiv> "rel_restrict_left :: (set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> 'a \<Rightarrow> bool)"
  set_rel_restrict_left_pred \<equiv> "rel_restrict_left :: set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set"
  set_rel_restrict_left_set \<equiv> "rel_restrict_left :: set \<Rightarrow> set \<Rightarrow> set"
  rel_restrict_right_set \<equiv> "rel_restrict_right :: ('a \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> ('a \<Rightarrow> set \<Rightarrow> bool)"
  set_rel_restrict_right_pred \<equiv> "rel_restrict_right :: set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set"
  set_rel_restrict_right_set \<equiv> "rel_restrict_right :: set \<Rightarrow> set \<Rightarrow> set"
begin
  definition "rel_restrict_left_set (R :: set \<Rightarrow> 'a \<Rightarrow> bool) A \<equiv> rel_restrict_left R (mem_of A)"
  definition "set_rel_restrict_left_pred R P \<equiv> {p \<in> R | \<exists>x y. P x \<and> p = \<langle>x, y\<rangle>}"
  definition "set_rel_restrict_left_set (R :: set) A \<equiv> rel_restrict_left R (mem_of A)"
  definition "rel_restrict_right_set (R :: 'a \<Rightarrow> set \<Rightarrow> bool) A \<equiv> rel_restrict_right R (mem_of A)"
  definition "set_rel_restrict_right_pred R P \<equiv> {p \<in> R | \<exists>x y. P y \<and> p = \<langle>x, y\<rangle>}"
  definition "set_rel_restrict_right_set (R :: set) A \<equiv> rel_restrict_right R (mem_of A)"
end

lemma rel_restrict_left_set_eq_rel_restrict_left [simp]: "(R :: set \<Rightarrow> 'a \<Rightarrow> bool)\<restriction>\<^bsub>A :: set\<^esub> = R\<restriction>\<^bsub>mem_of A\<^esub>"
  unfolding rel_restrict_left_set_def by simp

lemma rel_restrict_left_set_eq_rel_restrict_left_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "(R :: set \<Rightarrow> 'a \<Rightarrow> bool)\<restriction>\<^bsub>A :: set\<^esub> \<equiv> R\<restriction>\<^bsub>P\<^esub>"
  using assms by simp

lemma mem_rel_restrict_leftI:
  assumes "is_pair p"
  and "p \<in> R"
  and "P (fst p)"
  shows "p \<in> R\<restriction>\<^bsub>P\<^esub>"
  using assms unfolding set_rel_restrict_left_pred_def by auto

lemma pair_mem_rel_restrict_leftI [intro]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  and "P x"
  shows "\<langle>x, y\<rangle> \<in> R\<restriction>\<^bsub>P\<^esub>"
  using assms by (auto intro: mem_rel_restrict_leftI)

lemma mem_rel_restrict_leftE [elim]:
  assumes "p \<in> R\<restriction>\<^bsub>P\<^esub>"
  obtains x y where "p = \<langle>x, y\<rangle>" "P x" "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding set_rel_restrict_left_pred_def by blast

lemma set_rel_restrict_left_set_eq_set_rel_restrict_left [simp]: "(R :: set)\<restriction>\<^bsub>A :: set\<^esub> = R\<restriction>\<^bsub>mem_of A\<^esub>"
  unfolding set_rel_restrict_left_set_def by simp

lemma set_rel_restrict_left_set_eq_set_rel_restrict_left_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "(R :: set)\<restriction>\<^bsub>A :: set\<^esub> \<equiv> R\<restriction>\<^bsub>P\<^esub>"
  using assms by simp

lemma rel_restrict_right_set_eq_rel_restrict_right [simp]: "(R :: 'a \<Rightarrow> set \<Rightarrow> bool)\<upharpoonleft>\<^bsub>A :: set\<^esub> = R\<upharpoonleft>\<^bsub>mem_of A\<^esub>"
  unfolding rel_restrict_right_set_def by simp

lemma set_rel_restrict_right_eq_rel_restrict_right_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "(R :: 'a \<Rightarrow> set \<Rightarrow> bool)\<upharpoonleft>\<^bsub>A :: set\<^esub> \<equiv> R\<upharpoonleft>\<^bsub>P\<^esub>"
  using assms by simp

lemma mem_rel_restrict_rightI:
  assumes "is_pair p"
  and "p \<in> R"
  and "P (snd p)"
  shows "p \<in> R\<upharpoonleft>\<^bsub>P\<^esub>"
  using assms unfolding set_rel_restrict_right_pred_def by auto

lemma pair_mem_rel_restrict_rightI [intro]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  and "P y"
  shows "\<langle>x, y\<rangle> \<in> R\<upharpoonleft>\<^bsub>P\<^esub>"
  using assms by (auto intro: mem_rel_restrict_rightI)

lemma mem_rel_restrict_rightE [elim]:
  assumes "p \<in> R\<upharpoonleft>\<^bsub>P\<^esub>"
  obtains x y where "p = \<langle>x, y\<rangle>" "P y" "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding set_rel_restrict_right_pred_def by blast

lemma set_rel_restrict_right_set_eq_set_rel_restrict_right [simp]: "(R :: set)\<upharpoonleft>\<^bsub>A :: set\<^esub> = R\<upharpoonleft>\<^bsub>mem_of A\<^esub>"
  unfolding set_rel_restrict_right_set_def by simp

lemma set_rel_restrict_right_set_eq_set_rel_restrict_right_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "(R :: set)\<upharpoonleft>\<^bsub>A :: set\<^esub> \<equiv> R\<upharpoonleft>\<^bsub>P\<^esub>"
  using assms by simp

context
  fixes R :: "set" and P :: "set \<Rightarrow> bool"
begin

lemma set_rel_restrict_right_eq: "R\<upharpoonleft>\<^bsub>P\<^esub> = ((R\<inverse>)\<restriction>\<^bsub>P\<^esub>)\<inverse>"
  by blast

lemma set_rel_inv_restrict_right_rel_inv_eq_restrict_left [simp]: "((R\<inverse>)\<upharpoonleft>\<^bsub>P\<^esub>)\<inverse> = R\<restriction>\<^bsub>P\<^esub>"
  by blast

lemma mem_rel_restrict_right_iff_restrict_left: "\<langle>x, y\<rangle> \<in> R\<upharpoonleft>\<^bsub>P\<^esub> \<longleftrightarrow> \<langle>y, x\<rangle> \<in> (R\<inverse>)\<restriction>\<^bsub>P\<^esub>"
  unfolding set_rel_restrict_right_eq by simp

end

lemma set_restrict_left_empty_eq [simp]: "{}\<restriction>\<^bsub>P :: set \<Rightarrow> bool\<^esub> = {}" by auto

lemma set_restrict_left_empty_eq' [simp]: "R\<restriction>\<^bsub>{}\<^esub> = {}" by auto

lemma set_restrict_left_subset_self: "R\<restriction>\<^bsub>P :: set \<Rightarrow> bool\<^esub> \<subseteq> R" by auto

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

lemma set_restrict_left_restrict_left_eq_restrict_left [simp]:
  fixes R :: set and P :: "set \<Rightarrow> bool"
  shows "(R\<restriction>\<^bsub>P\<^esub>)\<restriction>\<^bsub>P\<^esub> = R\<restriction>\<^bsub>P\<^esub>"
  by auto

lemma mono_subset_set_restrict_left:
  "((\<subseteq>) \<Rrightarrow>\<^sub>m (\<le>) \<Rrightarrow> (\<subseteq>)) (rel_restrict_left :: set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set)"
  by fastforce

lemma set_rel_inv_rel_restrict_left_inv_rel_restrict_left_eq:
  fixes R :: "set" and P :: "set \<Rightarrow> bool" and Q :: "set \<Rightarrow> bool"
  shows "(((R\<restriction>\<^bsub>P\<^esub>)\<inverse>)\<restriction>\<^bsub>Q\<^esub>)\<inverse> = (((R\<inverse>)\<restriction>\<^bsub>Q\<^esub>)\<inverse>)\<restriction>\<^bsub>P\<^esub>"
  by (intro eqI' iffI mem_rel_restrict_leftI) (auto elim!: mem_rel_restrict_leftE)

lemma set_rel_restrict_left_right_eq_restrict_right_left:
  fixes R :: "set" and P :: "set \<Rightarrow> bool" and Q :: "set \<Rightarrow> bool"
  shows "R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> = R\<upharpoonleft>\<^bsub>Q\<^esub>\<restriction>\<^bsub>P\<^esub>"
  unfolding set_rel_restrict_right_eq
  by (fact set_rel_inv_rel_restrict_left_inv_rel_restrict_left_eq)

lemma dom_restrict_left_eq [simp]: "dom (R\<restriction>\<^bsub>P\<^esub>) = {x \<in> dom R | P x}"
  by auto

lemma dom_restrict_left_set_eq [simp]: "dom (R\<restriction>\<^bsub>A\<^esub>) = dom R \<inter> A" by simp

lemma mem_dom_rel_restrict_left_if_mem_dom [intro]:
  assumes "x \<in> dom R"
  and "P x"
  shows "x \<in> dom R\<restriction>\<^bsub>P\<^esub>"
  using assms by blast

lemma mem_dom_rel_restrict_leftE [elim]:
  assumes "x \<in> dom R\<restriction>\<^bsub>P\<^esub>"
  obtains y where "P x" "\<langle>x, y\<rangle> \<in> R"
  using assms by blast

lemma mem_codom_rel_restrict_leftI [intro]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  and "P x"
  shows "y \<in> codom R\<restriction>\<^bsub>P\<^esub>"
  using assms by blast

lemma mem_codom_rel_restrict_leftE [elim]:
  assumes "y \<in> codom R\<restriction>\<^bsub>P\<^esub>"
  obtains x where "P x" "\<langle>x, y\<rangle> \<in> R"
  using assms by blast

lemma rel_rel_restrict_left_eq_restrict_left_rel [simp, set_to_HOL_simp]:
  "rel ((R :: set)\<restriction>\<^bsub>P :: set \<Rightarrow> bool\<^esub>) = (rel R)\<restriction>\<^bsub>P\<^esub>"
  by auto

lemma rel_rel_restrict_right_eq_restrict_right_rel [simp, set_to_HOL_simp]:
  "rel ((R :: set)\<upharpoonleft>\<^bsub>P :: set \<Rightarrow> bool\<^esub>) = (rel R)\<upharpoonleft>\<^bsub>P\<^esub>"
  by auto

subsubsection \<open>Agreement\<close>

consts agree :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  agree_pred_set \<equiv> "agree :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  agree_set_set \<equiv> "agree :: set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "agree_pred_set (P :: set \<Rightarrow> bool) \<R> \<equiv> \<forall>R R' \<in> \<R>. R\<restriction>\<^bsub>P\<^esub> = R'\<restriction>\<^bsub>P\<^esub>"
  definition "(agree_set_set (A :: set) :: set \<Rightarrow> bool) \<equiv> agree (mem_of A)"
end

lemma agree_set_set_eq_agree_set [simp]: "(agree (A :: set) :: set \<Rightarrow> bool) = agree (mem_of A)"
  unfolding agree_set_set_def by simp

lemma agree_set_set_eq_agree_set_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "agree (A :: set) :: set \<Rightarrow> bool \<equiv> agree P"
  using assms by simp

lemma agree_set_set_iff_agree_set [iff]: "agree (A :: set) (\<R> :: set) \<longleftrightarrow> agree (mem_of A) \<R>"
  by simp

lemma agree_setI [intro]:
  assumes "\<And>x y R R'. P x \<Longrightarrow> R \<in> \<R> \<Longrightarrow> R' \<in> \<R> \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<Longrightarrow> \<langle>x, y\<rangle> \<in> R'"
  shows "agree P \<R>"
  using assms unfolding agree_pred_set_def by blast

lemma agree_setD:
  assumes "agree P \<R>"
  and "P x"
  and "R \<in> \<R>" "R' \<in> \<R>"
  and "\<langle>x, y\<rangle> \<in> R"
  shows "\<langle>x, y\<rangle> \<in> R'"
proof -
  from \<open>P x\<close> \<open>_ \<in> R\<close>  have "\<langle>x, y\<rangle> \<in> R\<restriction>\<^bsub>P\<^esub>" by auto
  moreover from assms have "... = R'\<restriction>\<^bsub>P\<^esub>" unfolding agree_pred_set_def by blast
  ultimately show ?thesis by auto
qed

lemma antimono_agree_set: "((\<le>) \<Rrightarrow>\<^sub>m (\<subseteq>) \<Rrightarrow> (\<ge>)) (agree :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool)"
  by (intro dep_mono_wrt_relI Dep_Fun_Rel_relI) (fastforce dest: agree_setD)

lemma set_restrict_left_eq_set_restrict_left_if_agree_set:
  fixes P :: "set \<Rightarrow> bool"
  assumes "agree P \<R>"
  and "R \<in> \<R>" "R' \<in> \<R>"
  shows "R\<restriction>\<^bsub>P\<^esub> = R'\<restriction>\<^bsub>P\<^esub>"
  using assms by (auto dest: agree_setD)

lemma eq_if_subset_dep_pairs_if_agree_set:
  assumes "agree A \<R>"
  and subset_dep_pairs: "\<And>R. R \<in> \<R> \<Longrightarrow> \<exists>B. R \<subseteq> \<Sum>x \<in> A. B x"
  and "R \<in> \<R>"
  and "R' \<in> \<R>"
  shows "R = R'"
proof -
  from subset_dep_pairs[OF \<open>R \<in> \<R>\<close>] have "R = R\<restriction>\<^bsub>A\<^esub>" by auto
  also with assms have "... = R'\<restriction>\<^bsub>A\<^esub>"
    supply set_rel_restrict_left_set_eq_set_rel_restrict_left[uhint]
    by (urule set_restrict_left_eq_set_restrict_left_if_agree_set where chained = insert)
    auto
  also from subset_dep_pairs[OF \<open>R' \<in> \<R>\<close>] have "... = R'" by auto
  finally show ?thesis .
qed

lemma subset_if_agree_set_if_subset_dep_pairs:
  assumes "R \<subseteq> \<Sum>x \<in> A. B x"
  and "R \<in> \<R>"
  and "agree A \<R>"
  and "R' \<in> \<R>"
  shows "R \<subseteq> R'"
  using assms by (auto simp: agree_setD[where ?R="R"])


subsubsection \<open>Diagonal\<close>

definition "diag A \<equiv> {\<langle>a, a\<rangle> | a \<in> A}"

lemma mem_diagI [intro!]: "p = \<langle>a, a\<rangle> \<Longrightarrow> a \<in> A \<Longrightarrow> p \<in> diag A"
  unfolding diag_def by auto

lemma mem_diagE [elim!]:
  assumes "p \<in> diag A"
  obtains a where "a \<in> A" "p = \<langle>a, a\<rangle>"
  using assms unfolding diag_def by auto

lemma mono_subset_diag: "((\<subseteq>) \<Rrightarrow>\<^sub>m (\<subseteq>)) diag"
  by auto


end
