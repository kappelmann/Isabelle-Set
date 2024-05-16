\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Functions on Relations\<close>
theory HOTG_Binary_Relation_Functions
  imports
    HOTG_Binary_Relations_Base
begin

subsubsection \<open>Domain, Codomain, and Field\<close>

definition "dom R \<equiv> {x | p \<in> R, \<exists>y. p = \<langle>x, y\<rangle>}"

lemma mem_domI [intro]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  shows "x \<in> dom R"
  using assms unfolding dom_def by auto

lemma mem_domE [elim!]:
  assumes "x \<in> dom R"
  obtains y where "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding dom_def by blast

lemma mem_of_dom_eq_in_dom_rel [simp, set_to_HOL_simp]: "mem_of (dom R) = in_dom (rel R)"
  by (intro ext) auto

lemma mono_subset_dom: "((\<subseteq>) \<Rightarrow> (\<subseteq>)) dom" by fast

context
  notes set_to_HOL_simp[simp]
begin

lemma dom_empty_eq [simp]: "dom {} = {}"
  by (urule in_dom_bottom_eq_bottom)

lemma dom_bin_union_eq [simp]: "dom (R \<union> S) = dom R \<union> dom S"
  by (urule in_dom_sup_eq_in_dom_sup_in_dom)

lemma dom_subset_if_dep_bin_rel:
  assumes "({\<Sum>}x : A. B x) R"
  shows "dom R \<subseteq> A"
  by (urule in_dom_le_if_dep_bin_rel) (use assms in blast)

end

lemma dom_union_eq [simp]: "dom (\<Union>\<R>) = \<Union>{dom R | R \<in> \<R>}" by auto

lemma dom_collect_eq [simp]: "dom {\<langle>f x, g x\<rangle> | x \<in> A} = {f x | x \<in> A}" by auto

lemma eq_dep_pair_if_mk_pair_mem_if_dep_bin_rel:
  assumes "({\<Sum>}x : A. B x) R"
  and "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B x \<Longrightarrow> \<langle>x, y\<rangle> \<in> R"
  shows "R = (\<Sum>x : A. B x)"
  using assms by auto

lemma dom_dep_pair_eq_if_ne_empty [simp]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> B x \<noteq> {}"
  shows "dom (\<Sum>x : A. B x) = A"
  using assms by (intro eqI') auto

definition "codom R \<equiv> {y | p \<in> R, \<exists>x. p = \<langle>x, y\<rangle>}"

lemma mem_codomI [intro]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  shows "y \<in> codom R"
  using assms unfolding codom_def by fast

lemma mem_codomE [elim!]:
  assumes "y \<in> codom R"
  obtains x where "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding codom_def by blast

lemma mem_of_codom_eq_in_codom_rel [simp, set_to_HOL_simp]: "mem_of (codom R) = in_codom (rel R)"
  by (intro ext) auto

lemma mono_subset_codom: "((\<subseteq>) \<Rightarrow> (\<subseteq>)) codom" by fast

context
  notes set_to_HOL_simp[simp] in_codom_eq_in_codom_on_top[simp]
begin

lemma codom_empty_eq [simp]: "codom {} = {}"
  by (urule in_codom_bottom_pred_eq_bottom)

lemma codom_bin_union_eq [simp]: "codom (R \<union> S) = codom R \<union> codom S"
  by (urule in_codom_on_sup_rel_eq_in_codom_on_sup_in_codom_on)

end

lemma codom_union_eq [simp]: "codom (\<Union>\<R>) = \<Union>{codom R | R \<in> \<R>}"
  by auto

lemma codom_collect_eq [simp]: "codom {\<langle>f x, g x\<rangle> | x \<in> A} = {g x | x \<in> A}"
  by auto

lemma codom_dep_pair_eq_idx_union [simp]: "codom (\<Sum>x : A. B x) = (\<Union>x \<in> A. B x)" by auto

lemma codom_subset_idx_union_if_dep_bin_rel:
  assumes "({\<Sum>}x : A. B x) R"
  shows "codom R \<subseteq> (\<Union>x \<in> A. B x)"
  using assms by (intro subsetI) auto

definition "field R \<equiv> dom R \<union> codom R"

lemma field_eq_dom_bin_union_codom: "field R = dom R \<union> codom R"
  unfolding field_def by auto

lemma mem_field_iff_mem_dom_or_codom [iff]: "x \<in> field R \<longleftrightarrow> x \<in> dom R \<or> x \<in> codom R"
  unfolding field_def by auto

lemma mono_subset_field: "((\<subseteq>) \<Rightarrow> (\<subseteq>)) field" by fast

lemma mem_of_field_eq_in_field_rel [simp, set_to_HOL_simp]: "mem_of (field R) = in_field (rel R)"
  by (intro ext) auto

context
  notes set_to_HOL_simp[simp]
begin

lemma field_empty_eq [simp]: "field {} = {}"
  by (urule in_field_bottom_eq_bottom)

lemma field_bin_union_eq [simp]: "field (R \<union> S) = field R \<union> field S"
  by (urule in_field_sup_eq_in_field_sup_in_field)

end

lemma field_union_eq [simp]: "field (\<Union>\<R>) = \<Union>{field R | R \<in> \<R>}"
  by blast

lemma field_collect_eq [simp]: "field {\<langle>f x, g x\<rangle> | x \<in> A} = ({f x | x \<in> A} \<union> {g x | x \<in> A})"
  by blast


subsubsection \<open>Composition\<close>

definition "rel_comp_set R S \<equiv> {p \<in> dom R \<times> codom S | \<exists>z. \<langle>fst p, z\<rangle> \<in> R \<and> \<langle>z, snd p\<rangle> \<in> S}"
adhoc_overloading rel_comp rel_comp_set

lemma mem_rel_compI:
  assumes "is_pair p"
  and "\<langle>fst p, y\<rangle> \<in> R"
  and "\<langle>y, snd p\<rangle> \<in> S"
  shows "p \<in> R \<circ>\<circ> S"
  using assms unfolding rel_comp_set_def by force

lemma mk_pair_mem_rel_compI [intro]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  and "\<langle>y, z\<rangle> \<in> S"
  shows "\<langle>x, z\<rangle> \<in> R \<circ>\<circ> S"
  using assms by (auto intro: mem_rel_compI)

lemma mem_rel_compE [elim]:
  assumes "p \<in> R \<circ>\<circ> S"
  obtains x y z where "\<langle>x, y\<rangle> \<in> R" "\<langle>y, z\<rangle> \<in> S" "p = \<langle>x, z\<rangle>"
  using assms unfolding rel_comp_set_def by auto

lemma is_bin_rel_set_rel_comp [iff]: "is_bin_rel (R \<circ>\<circ> S)" by fast

lemma rel_rel_comp_eq_rel_comp_rel [simp, set_to_HOL_simp]:
  "rel (R \<circ>\<circ> S) = rel R \<circ>\<circ> rel S"
  by (intro ext) auto

lemma mono_subset_rel_comp: "((\<subseteq>) \<Rightarrow> (\<subseteq>) \<Rrightarrow> (\<subseteq>)) (\<circ>\<circ>)" by fast

context
  notes set_to_HOL_simp[simp]
begin

lemma rel_comp_set_assoc: "(R :: set) \<circ>\<circ> (S \<circ>\<circ> T) = (R \<circ>\<circ> S) \<circ>\<circ> T"
  by (urule rel_comp_assoc)

lemma dom_rel_comp_subset_dom: "dom (R \<circ>\<circ> S) \<subseteq> dom R"
  by (urule subsetI, urule in_dom_if_in_dom_rel_comp) simp

lemma codom_rel_comp_subset_codom: "codom (R \<circ>\<circ> S) \<subseteq> codom S"
  by (urule subsetI, urule in_codom_if_in_codom_rel_comp) simp

lemma field_rel_comp_subset_dom_bin_union_codom: "field (R \<circ>\<circ> S) \<subseteq> dom R \<union> codom S"
  by (urule subsetI, urule (e) in_field_compE) simp_all

end

lemma mono_bin_rel_dep_bin_rel_bin_rel_idx_union_rel_comp_set:
  "(A {\<times>} B \<Rightarrow> ({\<Sum>}x : B. C x) \<Rightarrow> A {\<times>} (\<Union>x \<in> B. C x)) ((\<circ>\<circ>) :: set \<Rightarrow> _)"
  by (urule (rr) mono_wrt_predI set_bin_relI) force+

lemma set_pair_comp_dep_pair_eq_pair_idx_union [simp]:
  "((A \<times> B :: set) \<circ>\<circ> (\<Sum>x : B. C x)) = A \<times> (\<Union>x \<in> B. C x)"
  by auto


subsubsection \<open>Inverse\<close>

definition "rel_inv_set R \<equiv> {swap p | p \<in> {p \<in> R | is_pair p}}"
adhoc_overloading rel_inv rel_inv_set

lemma mem_rel_invI:
  assumes "is_pair p"
  assumes "\<langle>snd p, fst p\<rangle> \<in> R"
  shows "p \<in> R\<inverse>"
  using assms unfolding rel_inv_set_def by auto

lemma mk_pair_mem_rel_invI [intro]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  shows "\<langle>y, x\<rangle> \<in> R\<inverse>"
  using assms by (auto intro: mem_rel_invI)

lemma mem_rel_invE [elim!]:
  assumes "p \<in> R\<inverse>"
  obtains x y where "p = \<langle>y, x\<rangle>" "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding rel_inv_set_def by auto

lemma is_bin_rel_rel_inv_set [iff]: "is_bin_rel R\<inverse>" by fast

lemma rel_rel_inv_eq_rel_inv_rel [simp, set_to_HOL_simp]: "rel R\<inverse> = (rel R)\<inverse>"
  by auto

lemma mono_dep_bin_rel_idx_union_bin_rel_rel_inv:
  "(({\<Sum>}x : A. B x) \<Rightarrow> (\<Union>x \<in> A. B x) {\<times>} A) (rel_inv :: set \<Rightarrow> _)"
  by fast

lemma mono_bin_rel_rel_inv_set: "((A :: set) {\<times>} B \<Rightarrow> B {\<times>} A) (rel_inv :: set \<Rightarrow> _)"
  by force

lemma mono_subset_rel_inv_set: "((\<subseteq>) \<Rightarrow> (\<subseteq>)) rel_inv" by fast

lemma rel_inv_set_pair_eq [simp]: "(A \<times> B :: set)\<inverse> = B \<times> A"
  by auto

lemma mem_rel_inv_iff_mem [iff]: "\<langle>x, y\<rangle> \<in> R\<inverse> \<longleftrightarrow> \<langle>y, x\<rangle> \<in> R"
  supply set_to_HOL_simp[uhint] by (urule rel_inv_iff_rel)

lemma rel_inv_inv_eq_collect_is_pair [simp]: "R\<inverse>\<inverse> = {p \<in> R | is_pair p}"
  by auto

context
  notes set_to_HOL_simp[simp]
begin

lemma dom_rel_inv_eq_codom [simp]: "dom R\<inverse> = codom R"
  by (urule in_dom_rel_inv_eq_in_codom)

lemma codom_rel_inv_eq_dom [simp]: "codom R\<inverse> = dom R"
  by (urule in_codom_rel_inv_eq_in_dom)

lemma field_rel_inv_eq [simp]: "field R\<inverse> = field R"
  by (urule in_field_rel_inv_eq_in_field)

lemma rel_inv_set_comp_eq [simp]: "((R :: set) \<circ>\<circ> S)\<inverse> = S\<inverse> \<circ>\<circ> R\<inverse>"
  by (urule rel_inv_comp_eq)

lemma rel_inv_set_empty_eq [simp]: "{}\<inverse> = {}"
  by (urule rel_inv_bottom_eq)

end


subsubsection \<open>Restrictions\<close>

definition "rel_restrict_left_set (R :: set \<Rightarrow> 'a \<Rightarrow> bool) A \<equiv> rel_restrict_left R (mem_of A)"
adhoc_overloading rel_restrict_left rel_restrict_left_set

lemma rel_restrict_left_set_eq_rel_restrict_left_pred [simp]: "(R :: set \<Rightarrow> 'a \<Rightarrow> bool)\<restriction>\<^bsub>A\<^esub> = R\<restriction>\<^bsub>mem_of A\<^esub>"
  unfolding rel_restrict_left_set_def by simp

lemma rel_restrict_left_set_eq_rel_restrict_left_pred_uhint [uhint]:
  assumes "R \<equiv> R'"
  and "P \<equiv> mem_of A"
  shows "(R :: set \<Rightarrow> 'a \<Rightarrow> bool)\<restriction>\<^bsub>A\<^esub> \<equiv> R'\<restriction>\<^bsub>P\<^esub>"
  using assms by simp

definition "set_rel_restrict_left_pred R P \<equiv> {p \<in> R | is_pair p \<and> P (fst p)}"
adhoc_overloading rel_restrict_left set_rel_restrict_left_pred

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
  using assms unfolding set_rel_restrict_left_pred_def by auto

lemma is_bin_rel_set_rel_restrict_left [iff]: "is_bin_rel R\<restriction>\<^bsub>P\<^esub>" by fast

lemma rel_restrict_left_eq_restrict_left_rel [simp, set_to_HOL_simp]:
  "rel (R\<restriction>\<^bsub>P :: set \<Rightarrow> bool\<^esub>) = (rel R)\<restriction>\<^bsub>P\<^esub>"
  by auto

lemma dom_rel_restrict_left_eq [simp]: "dom R\<restriction>\<^bsub>P\<^esub> = {x \<in> dom R | P x}" by auto

lemma set_dep_pair_restrict_left_eq_dep_pair_collect [simp]:
  "(\<Sum>x : A. B x :: set)\<restriction>\<^bsub>P\<^esub> = (\<Sum>x : {a \<in> A | P a}. B x)"
  by auto

context
  notes set_to_HOL_simp[simp, symmetric, simp del]
begin

lemma set_rel_restrict_left_cong:
  assumes "\<And>x. P x \<longleftrightarrow> P' x"
  and "\<And>x y. P' x \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<longleftrightarrow> \<langle>x, y\<rangle> \<in> R'"
  shows "R\<restriction>\<^bsub>P\<^esub> = R'\<restriction>\<^bsub>P'\<^esub>"
  by (urule rel_restrict_left_cong) (use assms in auto)

lemma set_rel_restrict_left_top_eq_if_is_bin_rel [simp]:
  assumes [simp]: "is_bin_rel R"
  shows "(R :: set)\<restriction>\<^bsub>\<top> :: set \<Rightarrow> bool\<^esub> = R"
  by (urule rel_restrict_left_top_eq)

lemma set_rel_restrict_left_bottom_eq [simp]: "(R :: set)\<restriction>\<^bsub>\<bottom> :: set \<Rightarrow> bool\<^esub> = {}"
  by (urule rel_restrict_left_bottom_eq)

lemma empty_restrict_left_eq [simp]: "{}\<restriction>\<^bsub>P :: set \<Rightarrow> bool\<^esub> = {}"
  by (urule bottom_restrict_left_eq)

lemma rel_restrict_left_subset_self: "R\<restriction>\<^bsub>(P :: set \<Rightarrow> bool)\<^esub> \<subseteq> R"
  by (urule rel_restrict_left_le_self)

lemma subset_rel_restrict_left_self_if_mem_of_dom_le_if_is_bin_rel:
  assumes [simp]: "is_bin_rel R"
  and "mem_of (dom R) \<le> P"
  shows "R \<subseteq> R\<restriction>\<^bsub>(P :: set \<Rightarrow> bool)\<^esub>"
  by (urule le_rel_restrict_left_self_if_in_dom_le) (use assms in fast)

corollary set_rel_restrict_left_eq_self_if_mem_of_dom_le_if_is_bin_rel:
  assumes [simp]: "is_bin_rel R"
  and "mem_of (dom R) \<le> P"
  shows "R\<restriction>\<^bsub>P\<^esub> = R"
  by (urule rel_restrict_left_eq_self_if_in_dom_le) (use assms in fast)

lemma set_rel_restrict_left_eq_self_if_set_dep_bin_rel [simp]:
  assumes [simp]: "({\<Sum>}x : (A :: set \<Rightarrow> bool). B x) (R :: set)"
  shows "R\<restriction>\<^bsub>A\<^esub> = R"
  supply is_bin_rel_if_set_dep_bin_rel[of A B, simp]
  by (urule rel_restrict_left_eq_self_if_dep_bin_rel) (use assms in blast)

end


lemma mono_dep_bin_rel_top_dep_bin_rel_inf_set_rel_restrict_left:
  "(({\<Sum>}x : A. B x) \<Rightarrow> (P : \<top>) \<Rightarrow> ({\<Sum>}x : A \<sqinter> P. B x)) (rel_restrict_left :: set \<Rightarrow> _)"
  by fast

lemma mono_subset_rel_restrict_left: "((\<subseteq>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<subseteq>)) rel_restrict_left" by fast


definition "set_rel_restrict_left_set (R :: set) A \<equiv> rel_restrict_left R (mem_of A)"
adhoc_overloading rel_restrict_left set_rel_restrict_left_set

lemma set_rel_restrict_left_set_eq_set_rel_restrict_left_pred [simp]: "(R :: set)\<restriction>\<^bsub>A\<^esub> = R\<restriction>\<^bsub>mem_of A\<^esub>"
  unfolding set_rel_restrict_left_set_def by simp

lemma set_rel_restrict_left_set_eq_set_rel_restrict_left_pred_uhint [uhint]:
  assumes "R \<equiv> R'"
  and "P \<equiv> mem_of A"
  shows "(R :: set)\<restriction>\<^bsub>A\<^esub> \<equiv> R'\<restriction>\<^bsub>P\<^esub>"
  using assms by simp

definition "rel_restrict_right_set (R :: 'a \<Rightarrow> set \<Rightarrow> bool) A \<equiv> rel_restrict_right R (mem_of A)"
adhoc_overloading rel_restrict_right rel_restrict_right_set

lemma rel_restrict_right_set_eq_rel_restrict_right_pred [simp]:
  "(R :: 'a \<Rightarrow> set \<Rightarrow> bool)\<upharpoonleft>\<^bsub>A\<^esub> = R\<upharpoonleft>\<^bsub>mem_of A\<^esub>"
  unfolding rel_restrict_right_set_def by simp

lemma set_rel_restrict_right_eq_rel_restrict_right_pred_uhint [uhint]:
  assumes "R \<equiv> R'"
  and "P \<equiv> mem_of A"
  shows "(R :: 'a \<Rightarrow> set \<Rightarrow> bool)\<upharpoonleft>\<^bsub>A\<^esub> \<equiv> R'\<upharpoonleft>\<^bsub>P\<^esub>"
  using assms by simp

definition "set_rel_restrict_right_pred R P \<equiv> {p \<in> R | is_pair p \<and> P (snd p)}"
adhoc_overloading rel_restrict_right set_rel_restrict_right_pred

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
  using assms unfolding set_rel_restrict_right_pred_def by auto

lemma is_bin_rel_set_rel_restrict_right [iff]: "is_bin_rel R\<upharpoonleft>\<^bsub>P\<^esub>" by fast

lemma rel_restrict_right_eq_restrict_right_rel [simp,set_to_HOL_simp]:
  "rel (R\<upharpoonleft>\<^bsub>P :: set \<Rightarrow> bool\<^esub>) = (rel R)\<upharpoonleft>\<^bsub>P\<^esub>"
  by auto

lemma codom_rel_restrict_right_eq [simp]: "codom R\<upharpoonleft>\<^bsub>P\<^esub> = {x \<in> codom R | P x}" by auto

lemma set_dep_pair_restrict_right_eq_dep_pair_collect [simp]:
  "(\<Sum>x : A. B x :: set)\<upharpoonleft>\<^bsub>P\<^esub> = (\<Sum>x : A. {y \<in> B x | P y})"
  by auto

context
  notes set_to_HOL_simp[simp, symmetric, simp del]
begin

lemma rel_restrict_right_cong:
  assumes "\<And>y. P y \<longleftrightarrow> P' y"
  and "\<And>x y. P' y \<Longrightarrow>  \<langle>x, y\<rangle> \<in> R \<longleftrightarrow> \<langle>x, y\<rangle> \<in> R'"
  shows "R\<upharpoonleft>\<^bsub>P\<^esub> = R'\<upharpoonleft>\<^bsub>P'\<^esub>"
  by (urule rel_restrict_right_cong) (use assms in auto)

lemma set_rel_restrict_right_top_eq_if_is_bin_rel [simp]:
  assumes [simp]: "is_bin_rel R"
  shows "(R :: set)\<upharpoonleft>\<^bsub>\<top> :: set \<Rightarrow> bool\<^esub> = R"
  by (urule rel_restrict_right_top_eq)

lemma set_rel_restrict_right_bottom_eq [simp]: "(R :: set)\<upharpoonleft>\<^bsub>\<bottom> :: set \<Rightarrow> bool\<^esub> = {}"
  by (urule rel_restrict_right_bottom_eq)

lemma empty_restrict_right_eq [simp]: "{}\<upharpoonleft>\<^bsub>P :: set \<Rightarrow> bool\<^esub> = {}"
  by (urule bottom_restrict_right_eq)

lemma rel_restrict_right_subset_self: "R\<upharpoonleft>\<^bsub>(P :: set \<Rightarrow> bool)\<^esub> \<subseteq> R"
  by (urule rel_restrict_right_le_self)

lemma subset_rel_restrict_right_self_if_mem_of_codom_le_if_is_bin_rel:
  assumes [simp]: "is_bin_rel R"
  and "mem_of (codom R) \<le> P"
  shows "R \<subseteq> R\<upharpoonleft>\<^bsub>(P :: set \<Rightarrow> bool)\<^esub>"
  by (urule le_rel_restrict_right_self_if_in_codom_le) (use assms in fast)

corollary set_rel_restrict_right_eq_self_if_mem_of_codom_le:
  assumes [simp]: "is_bin_rel R"
  and "mem_of (codom R) \<le> P"
  shows "R\<upharpoonleft>\<^bsub>P\<^esub> = R"
  by (urule rel_restrict_right_eq_self_if_in_codom_le) (use assms in fast)

lemma mono_dep_bin_rel_top_dep_bin_rel_inf_set_rel_restrict_right:
  "(({\<Sum>}x : A. B x) \<Rightarrow> (P : \<top>) \<Rightarrow> ({\<Sum>}x : A. (B x) \<sqinter> P)) (rel_restrict_right :: set \<Rightarrow> _)"
  by fast

lemma mono_subset_rel_restrict_right: "((\<subseteq>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<subseteq>)) rel_restrict_right" by fast

context
  fixes R :: "set" and P Q :: "set \<Rightarrow> bool"
begin

lemma set_rel_restrict_right_eq: "R\<upharpoonleft>\<^bsub>P\<^esub> = ((R\<inverse>)\<restriction>\<^bsub>P\<^esub>)\<inverse>"
  by (urule rel_restrict_right_eq)

lemma set_rel_inv_restrict_right_rel_inv_eq_restrict_left [simp]: "((R\<inverse>)\<upharpoonleft>\<^bsub>P\<^esub>)\<inverse> = R\<restriction>\<^bsub>P\<^esub>"
  by (urule rel_inv_restrict_right_rel_inv_eq_restrict_left)

lemma set_rel_restrict_right_iff_restrict_left: "\<langle>x, y\<rangle> \<in> R\<upharpoonleft>\<^bsub>P\<^esub> \<longleftrightarrow> \<langle>y, x\<rangle> \<in> R\<inverse>\<restriction>\<^bsub>P\<^esub>"
  supply set_to_HOL_simp[simp del, symmetric, simp]
  by (urule rel_restrict_right_iff_restrict_left[of "rel _"])

lemma set_rel_inv_rel_restrict_left_inv_rel_restrict_left_eq: "(((R\<restriction>\<^bsub>P\<^esub>)\<inverse>)\<restriction>\<^bsub>Q\<^esub>)\<inverse> = (((R\<inverse>)\<restriction>\<^bsub>Q\<^esub>)\<inverse>)\<restriction>\<^bsub>P\<^esub>"
  by (urule rel_inv_rel_restrict_left_inv_rel_restrict_left_eq)

lemma set_rel_restrict_left_right_eq_set_restrict_right_left: "R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> = R\<upharpoonleft>\<^bsub>Q\<^esub>\<restriction>\<^bsub>P\<^esub>"
  by (urule rel_restrict_left_right_eq_restrict_right_left)

end
end

definition "set_rel_restrict_right_set (R :: set) A \<equiv> rel_restrict_right R (mem_of A)"
adhoc_overloading rel_restrict_right set_rel_restrict_right_set

lemma set_rel_restrict_right_set_eq_set_rel_restrict_right_pred [simp]: "(R :: set)\<upharpoonleft>\<^bsub>A\<^esub> = R\<upharpoonleft>\<^bsub>mem_of A\<^esub>"
  unfolding set_rel_restrict_right_set_def by simp

lemma set_rel_restrict_right_set_eq_set_rel_restrict_right_pred_uhint [uhint]:
  assumes "R \<equiv> R'"
  and "P \<equiv> mem_of A"
  shows "(R :: set)\<upharpoonleft>\<^bsub>A\<^esub> \<equiv> R'\<upharpoonleft>\<^bsub>P\<^esub>"
  using assms by simp


end
