section \<open>Binary Relations\<close>
theory Binary_Relations
  imports
    Pairs
    Replacement_Predicates
begin

subsection \<open>Predicates on Relations\<close>

consts injective :: "'a \<Rightarrow> set \<Rightarrow> bool"

overloading
  injective_pred \<equiv> "injective :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  injective_set \<equiv> "injective :: set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "injective_pred P R \<equiv> \<forall>y x x'. P y \<and> \<langle>x, y\<rangle> \<in> R \<and> \<langle>x', y\<rangle> \<in> R \<longrightarrow> x = x'"
  definition "injective_set B R \<equiv> injective (\<lambda>y. y \<in> B) R"
end

lemma injective_set_iff_injective [iff]:
  "injective B R \<longleftrightarrow> injective (\<lambda>y. y \<in> B) R"
  unfolding injective_set_def by simp

lemma injectiveI [intro]:
  assumes "\<And>x x' y. P y \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<Longrightarrow> \<langle>x', y\<rangle> \<in> R \<Longrightarrow> x = x'"
  shows "injective P R"
  using assms unfolding injective_set_def injective_pred_def by blast

lemma injectiveD:
  assumes "injective P R"
  and "P y"
  and "\<langle>x, y\<rangle> \<in> R" "\<langle>x', y\<rangle> \<in> R"
  shows "x = x'"
  using assms unfolding injective_pred_def by blast

lemma injective_contravariant_pred:
  fixes P :: "set \<Rightarrow> bool"
  assumes "injective P R"
  and "\<And>x. P' x \<Longrightarrow> P x"
  shows "injective P' R"
  using assms by (auto dest: injectiveD)

lemma injective_contravariant_set:
  fixes P :: "set \<Rightarrow> bool"
  assumes "injective P R"
  and "R' \<subseteq> R"
  shows "injective P R'"
  using assms by (auto dest: injectiveD)

consts right_unique :: "'a \<Rightarrow> set \<Rightarrow> bool"

overloading
  right_unique_pred \<equiv> "right_unique :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  right_unique_set \<equiv> "right_unique :: set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "right_unique_pred P R \<equiv> \<forall>x y y'. P x \<and> \<langle>x, y\<rangle> \<in> R \<and> \<langle>x, y'\<rangle> \<in> R \<longrightarrow> y = y'"
  definition "right_unique_set A R \<equiv> right_unique (\<lambda>x. x \<in> A) R"
end

lemma right_unique_set_iff_right_unique [iff]:
  "right_unique A R \<longleftrightarrow> right_unique (\<lambda>x. x \<in> A) R"
  unfolding right_unique_set_def by simp

lemma right_uniqueI [intro]:
  assumes "\<And>x y y'. P x \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<Longrightarrow> \<langle>x, y'\<rangle> \<in> R \<Longrightarrow> y = y'"
  shows "right_unique P R"
  using assms unfolding right_unique_pred_def by blast

lemma right_uniqueD:
  assumes "right_unique P R"
  and "P x"
  and "\<langle>x, y\<rangle> \<in> R" "\<langle>x, y'\<rangle> \<in> R"
  shows "y = y'"
  using assms unfolding right_unique_pred_def by blast

lemma right_unique_contravariant_pred:
  fixes P :: "set \<Rightarrow> bool"
  assumes "right_unique P R"
  and "\<And>x. P' x \<Longrightarrow> P x"
  shows "right_unique P' R"
  using assms by (auto dest: right_uniqueD)

lemma right_unique_contravariant_set:
  fixes P :: "set \<Rightarrow> bool"
  assumes "right_unique P R"
  and "R' \<subseteq> R"
  shows "right_unique P R'"
  using assms by (auto dest: right_uniqueD)


consts left_total :: "'a \<Rightarrow> set \<Rightarrow> bool"

overloading
  left_total_pred \<equiv> "left_total :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  left_total_set \<equiv> "left_total :: set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "left_total_pred P R \<equiv> \<forall>x. P x \<longrightarrow> (\<exists>y. \<langle>x, y\<rangle> \<in> R)"
  definition "left_total_set A R \<equiv> left_total (\<lambda>x. x \<in> A) R"
end

lemma left_total_set_iff_left_total [iff]:
  "left_total A R \<longleftrightarrow> left_total (\<lambda>x. x \<in> A) R"
  unfolding left_total_set_def by simp

lemma left_totalI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> \<exists>y. \<langle>x, y\<rangle> \<in> R"
  shows "left_total P R"
  unfolding left_total_pred_def using assms by blast

lemma left_totalE [elim]:
  assumes "left_total P R"
  and "P x"
  obtains y where "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding left_total_pred_def by blast

lemma left_total_contravariant_pred:
  fixes P :: "set \<Rightarrow> bool"
  assumes "left_total P R"
  and "\<And>x. P' x \<Longrightarrow> P x"
  shows "left_total P' R"
  using assms by (intro left_totalI) auto

lemma left_total_covariant_set:
  fixes P :: "set \<Rightarrow> bool"
  assumes "left_total P R"
  and "R \<subseteq> R'"
  shows "left_total P R'"
  using assms by (intro left_totalI) auto


consts surjective :: "'a \<Rightarrow> set \<Rightarrow> bool"

overloading
  surjective_pred \<equiv> "surjective :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  surjective_set \<equiv> "surjective :: set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "surjective_pred P R \<equiv> \<forall>y. P y \<longrightarrow> (\<exists>x. \<langle>x, y\<rangle> \<in> R)"
  definition "surjective_set B R \<equiv> surjective (\<lambda>y. y \<in> B) R"
end

lemma surjective_set_iff_surjective [iff]:
  "surjective B R \<longleftrightarrow> surjective (\<lambda>y. y \<in> B) R"
  unfolding surjective_set_def by simp

lemma surjectiveI [intro]:
  assumes "\<And>y. P y \<Longrightarrow> \<exists>x. \<langle>x, y\<rangle> \<in> R"
  shows "surjective P R"
  unfolding surjective_pred_def using assms by blast

lemma surjectiveE [elim]:
  assumes "surjective P R"
  and "P y"
  obtains x where "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding surjective_pred_def by blast

lemma surjective_contravariant_pred:
  fixes P :: "set \<Rightarrow> bool"
  assumes "surjective P R"
  and "\<And>x. P' x \<Longrightarrow> P x"
  shows "surjective P' R"
  using assms by (intro surjectiveI) auto

lemma surjective_covariant_set:
  fixes P :: "set \<Rightarrow> bool"
  assumes "surjective P R"
  and "R \<subseteq> R'"
  shows "surjective P R'"
  using assms by (intro surjectiveI) auto


definition "connected D R \<equiv> \<forall>x y \<in> D. x \<noteq> y \<longrightarrow> \<langle>x, y\<rangle> \<in> R \<or> \<langle>y, x\<rangle> \<in> R"

lemma connectedI [intro]:
  assumes "\<And>x y. x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<or> \<langle>y, x\<rangle> \<in> R"
  shows "connected D R"
  using assms unfolding connected_def by blast

lemma connectedE:
  assumes "connected D R"
  and "x \<in> D" "y \<in> D"
  and "x \<noteq> y"
  obtains "\<langle>x, y\<rangle> \<in> R" | "\<langle>y, x\<rangle> \<in> R"
  using assms unfolding connected_def by auto


definition "reflexive D R \<equiv> \<forall>x \<in> D. \<langle>x, x\<rangle> \<in> R"

lemma reflexiveI [intro]:
  assumes "\<And>x. x \<in> D \<Longrightarrow> \<langle>x, x\<rangle> \<in> R"
  shows "reflexive D R"
  using assms unfolding reflexive_def by blast

lemma reflexiveD:
  assumes "reflexive D R"
  and "x \<in> D"
  shows "\<langle>x, x\<rangle> \<in> R"
  using assms unfolding reflexive_def by blast


definition "irreflexive D R \<equiv> \<forall>x \<in> D. \<langle>x, x\<rangle> \<notin> R"

lemma irreflexiveI [intro]:
  assumes "\<And>x. x \<in> D \<Longrightarrow> \<langle>x, x\<rangle> \<notin> R"
  shows "irreflexive D R"
  using assms unfolding irreflexive_def by blast

lemma irreflexiveD:
  assumes "irreflexive D R"
  and "x \<in> D"
  shows "\<langle>x, x\<rangle> \<notin> R"
  using assms unfolding irreflexive_def by blast


definition "symmetric D R \<equiv> \<forall>x y \<in> D. \<langle>x, y\<rangle> \<in> R \<longrightarrow> \<langle>y, x\<rangle> \<in> R"

lemma symmetricI [intro]:
  assumes "\<And>x y. x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<Longrightarrow> \<langle>y, x\<rangle> \<in> R"
  shows "symmetric D R"
  using assms unfolding symmetric_def by blast

lemma symmetricD:
  assumes "symmetric D R"
  and "x \<in> D" "y \<in> D"
  and "\<langle>x, y\<rangle> \<in> R"
  shows "\<langle>y, x\<rangle> \<in> R"
  using assms unfolding symmetric_def by blast


definition "antisymmetric D R \<equiv> \<forall>x y \<in> D. \<langle>x, y\<rangle> \<in> R \<and> \<langle>y, x\<rangle> \<in> R \<longrightarrow> x = y"

lemma antisymmetricI [intro]:
  assumes "\<And>x y. x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<Longrightarrow> \<langle>y, x\<rangle> \<in> R \<Longrightarrow> x = y"
  shows "antisymmetric D R"
  using assms unfolding antisymmetric_def by blast

lemma antisymmetricD:
  assumes "antisymmetric D R"
  and "x \<in> D" "y \<in> D"
  and "\<langle>x, y\<rangle> \<in> R" "\<langle>y, x\<rangle> \<in> R"
  shows "x = y"
  using assms unfolding antisymmetric_def by blast


definition "transitive D R \<equiv> \<forall>x y z \<in> D. \<langle>x, y\<rangle> \<in> R \<and> \<langle>y, z\<rangle> \<in> R \<longrightarrow> \<langle>x, z\<rangle> \<in> R"

lemma transitiveI [intro]:
  assumes
    "\<And>x y z. x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> z \<in> D \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<Longrightarrow> \<langle>y, z\<rangle> \<in> R \<Longrightarrow> \<langle>x, z\<rangle> \<in> R"
  shows "transitive D R"
  using assms unfolding transitive_def by blast

lemma transitiveD:
  assumes "transitive D R"
  and "x \<in> D" "y \<in> D" "z \<in> D"
  and "\<langle>x, y\<rangle> \<in> R" "\<langle>y, z\<rangle> \<in> R"
  shows "\<langle>x, z\<rangle> \<in> R"
  using assms unfolding transitive_def by blast


definition "partially_ordered D R \<equiv>
  reflexive D R \<and> antisymmetric D R \<and> transitive D R"

definition "linearly_ordered D R \<equiv> connected D R \<and> partially_ordered D R"

definition "well_founded D R \<equiv>
  \<forall>X. X \<subseteq> D \<and> X \<noteq> {} \<longrightarrow> (\<exists>a \<in> X. \<forall>x \<in> X. \<langle>x, a\<rangle> \<in> R \<longrightarrow> x = a)"

lemma well_foundedI:
  assumes "\<And>X. \<lbrakk>X \<subseteq> D; X \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>a \<in> X. \<forall>x \<in> X. \<langle>x, a\<rangle> \<in> R \<longrightarrow> x = a"
  shows "well_founded D R"
  using assms unfolding well_founded_def by auto

definition "well_ordered D R \<equiv> linearly_ordered D R \<and> well_founded D R"


subsection \<open>Functions on Relations\<close>

text \<open>Extensions and Restricts\<close>

definition "extend x y R \<equiv> insert \<langle>x, y\<rangle> R"

lemma mem_extendI [simp, intro!]: "\<langle>x, y\<rangle> \<in> extend x y R"
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

lemma glue_subset_glue_if_subset:
  assumes "\<R> \<subseteq> \<R>'"
  shows "glue \<R> \<subseteq> glue \<R>'"
  using assms by auto

lemma right_unique_glueI:
  fixes P :: "set \<Rightarrow> bool"
  assumes "\<And>R R'. R \<in> \<R> \<Longrightarrow> R' \<in> \<R> \<Longrightarrow> right_unique P (glue {R, R'})"
  shows "right_unique P (glue \<R>)"
proof
  fix x y y' assume "P x" "\<langle>x, y\<rangle> \<in> glue \<R>" "\<langle>x, y'\<rangle> \<in> glue \<R>"
  with assms obtain R R' where "R \<in> \<R>" "R' \<in> \<R>" "\<langle>x, y\<rangle> \<in> R" "\<langle>x, y'\<rangle> \<in> R'"
    and runique: "right_unique P (glue {R, R'})"
    by auto
  then have "\<langle>x, y\<rangle> \<in> (glue {R, R'})" "\<langle>x, y'\<rangle> \<in> (glue {R, R'})" by auto
  with \<open>P x\<close> runique show "y = y'" by (intro right_uniqueD)
qed


consts restrict :: "set \<Rightarrow> 'a \<Rightarrow> set"

bundle hotg_restrict_syntax begin notation restrict (infixl "\<restriction>" 100) end
bundle no_hotg_set_restrict_syntax begin no_notation restrict (infixl "\<restriction>" 100) end
unbundle hotg_restrict_syntax

overloading
  restrict_pred \<equiv> "restrict :: set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set"
  restrict_set \<equiv> "restrict :: set \<Rightarrow> set \<Rightarrow> set"
begin
  definition "restrict_pred R P \<equiv> {p \<in> R | \<exists>x y. P x \<and> p = \<langle>x, y\<rangle>}"
  definition "restrict_set R A \<equiv> restrict R (\<lambda>x. x \<in> A)"
end

lemma restrict_set_eq_restrict [simp]:
  "restrict R A = restrict R (\<lambda>x. x \<in> A)"
  unfolding restrict_set_def by simp

lemma mem_restrictI [intro!]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  and "P x"
  shows "\<langle>x, y\<rangle> \<in> R\<restriction>P"
  using assms unfolding restrict_pred_def by blast

lemma mem_restrictE [elim]:
  assumes "p \<in> R\<restriction>P"
  obtains x y where "p = \<langle>x, y\<rangle>" "P x" "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding restrict_pred_def by blast

lemma restrict_covariant_pred:
  fixes P :: "set \<Rightarrow> bool"
  assumes "\<And>x. P' x \<Longrightarrow> P x"
  shows "R\<restriction>P' \<subseteq> R\<restriction>P"
  using assms by auto

lemma restrict_covariant_set:
  fixes P :: "set \<Rightarrow> bool"
  assumes "R \<subseteq> R'"
  shows "R\<restriction>P \<subseteq> R'\<restriction>P"
  using assms by auto

lemma restrict_empty_eq [simp, intro!]: "{}\<restriction>(P :: set \<Rightarrow> bool) = {}" by auto

lemma restrict_empty_eq' [simp, intro!]: "R\<restriction>{} = {}" by auto

lemma restrict_subset_self [simp, intro!]: "R\<restriction>(P :: set \<Rightarrow> bool) \<subseteq> R" by auto

lemma restrict_dep_pairs_eq_dep_pairs_collect [simp]:
  "(\<Sum>x \<in> A. (B x))\<restriction>P = (\<Sum>x \<in> {a \<in> A | P a}. (B x))"
  by auto

lemma restrict_dep_pairs_eq_dep_pairs_bin_inter [simp]:
  "(\<Sum>x \<in> A. (B x))\<restriction>A' = (\<Sum>x \<in> A \<inter> A'. (B x))"
  by simp

lemma restrict_restrict_eq_restrict [simp]:
  fixes P P' :: "set \<Rightarrow> bool"
  shows "f\<restriction>P\<restriction>P = f\<restriction>P"
  by auto

lemma left_total_and_restrictI:
  fixes P P' :: "set \<Rightarrow> bool"
  assumes "left_total P R"
  shows "left_total (\<lambda>x. P x \<and> P' x) (R\<restriction>P')"
  using assms by (intro left_totalI) auto


definition "agree P \<R> \<equiv> \<forall>R R' \<in> \<R>. R\<restriction>P = R'\<restriction>P"

lemma agree_set_iff_agree [iff]:
  "agree A \<R> \<longleftrightarrow> agree (\<lambda>x. x \<in> A) \<R>"
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
  from assms(2, 5) have "\<langle>x, y\<rangle> \<in> R\<restriction>P" by (intro mem_restrictI)
  moreover from assms(1, 3-4) have "... = R'\<restriction>P" unfolding agree_def by blast
  ultimately show ?thesis by auto
qed

lemma agree_covariant_pred:
  fixes P :: "set \<Rightarrow> bool"
  assumes "agree P \<R>"
  and "\<And>x. P' x \<Longrightarrow> P x"
  shows "agree P' \<R>"
  using assms by (auto dest: agreeD)

lemma agree_covariant_set:
  fixes P :: "set \<Rightarrow> bool"
  assumes "agree P \<R>"
  and "\<R>' \<subseteq> \<R>"
  shows "agree P \<R>'"
  using assms by (auto dest: agreeD)

lemma restrict_eq_restrict_if_agree:
  fixes P :: "set \<Rightarrow> bool"
  assumes "agree P \<R>"
  and "R \<in> \<R>" "R' \<in> \<R>"
  shows "R\<restriction>P = R'\<restriction>P"
  using assms by (auto dest: agreeD)

lemma eq_if_subset_dep_pairs_if_agree:
  assumes "agree A \<R>"
  and subset_dep_pairs: "\<And>R. R \<in> \<R> \<Longrightarrow> \<exists>B. R \<subseteq> \<Sum>x \<in> A. (B x)"
  and "R \<in> \<R>"
  and "R' \<in> \<R>"
  shows "R = R'"
proof -
  from subset_dep_pairs[OF \<open>R \<in> \<R>\<close>] have "R = R\<restriction>A" by auto
  also with assms have "... = R'\<restriction>A"
    by ((subst restrict_set_eq_restrict)+, intro restrict_eq_restrict_if_agree)
      auto
  also from subset_dep_pairs[OF \<open>R' \<in> \<R>\<close>] have "... = R'" by auto
  finally show ?thesis .
qed

lemma subset_if_agree_if_subset_dep_pairs:
  assumes subset_dep_pairs: "R \<subseteq> \<Sum>x \<in> A. (B x)"
  and "R \<in> \<R>"
  and "agree A \<R>"
  and "R' \<in> \<R>"
  shows "R \<subseteq> R'"
  using assms by (auto simp: agreeD[where ?R="R"])


definition "dom R \<equiv> {x | p \<in> R, \<exists>y. p = \<langle>x, y\<rangle>}"

lemma mem_domI [intro]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  shows "x \<in> dom R"
  using assms unfolding dom_def by fast

lemma mem_domE [elim!]:
  assumes "x \<in> dom R"
  obtains y where "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding dom_def by blast

lemma dom_covariant:
  assumes "R \<subseteq> R'"
  shows "dom R \<subseteq> dom R'"
  using assms by auto

lemma dom_empty_eq [simp, intro!]: "dom {} = {}"
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
  shows "dom (\<Sum>x \<in> A. (B x)) = A"
  using assms by (intro eqI) auto

lemma dom_restrict_eq [simp]: "dom (R\<restriction>P) = {x \<in> dom R | P x}"
  by auto

lemma dom_restrict_set_eq [simp]: "dom (R\<restriction>A) = dom R \<inter> A" by simp

lemma subset_dom_if_left_total [simp]: "left_total A R \<Longrightarrow> A \<subseteq> dom R" by auto

lemma glue_subset_dep_pairsI:
  fixes \<R> defines "D \<equiv> \<Union>R \<in> \<R>. dom R"
  assumes all_subset_dep_pairs: "\<And>R. R \<in> \<R> \<Longrightarrow> \<exists>A. R \<subseteq> \<Sum>x \<in> A. (B x)"
  shows "glue \<R> \<subseteq> \<Sum>x \<in> D. (B x)"
proof
  fix p assume "p \<in> glue \<R>"
  with all_subset_dep_pairs obtain R A where "p \<in> R" "R \<in> \<R>" "R \<subseteq> \<Sum>x \<in> A. (B x)"
    by (auto 6 0)
  then obtain x y where "p = \<langle>x, y\<rangle>" "x \<in> dom R" "y \<in> B x"
    by (auto dest!: mem_if_mem_if_subset)
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

lemma rng_covariant:
  assumes "R \<subseteq> R'"
  shows "rng R \<subseteq> rng R'"
  using assms by auto

lemma rng_empty_eq [simp, intro!]: "rng {} = {}"
  by auto

lemma rng_union_eq [simp]: "rng (\<Union>\<R>) = \<Union>{rng R | R \<in> \<R>}"
  by auto

lemma rng_bin_union_eq [simp]: "rng (R \<union> S) = rng R \<union> rng S"
  by auto

lemma rng_collect_eq [simp]: "rng {\<langle>f x, g x\<rangle> | x \<in> A} = {g x | x \<in> A}"
  by auto

lemma rng_extend_eq [simp]: "rng (extend x y R) = insert y (rng R)"
  by (rule eqI) (auto intro: mem_extendI')

lemma rng_dep_pairs_eq [simp]: "rng (\<Sum>x \<in> A. (B x)) = (\<Union>x \<in> A. (B x))"
  by auto

lemma subset_rng_if_surjective [simp]: "surjective B R \<Longrightarrow> B \<subseteq> rng R"
  by auto


definition "converse R \<equiv> {\<langle>y, x\<rangle> | \<langle>x, y\<rangle> \<in> {p \<in> R | \<exists>x y. p = \<langle>x, y\<rangle>}}"

lemma mem_converseI [intro]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  shows "\<langle>y, x\<rangle> \<in> converse R"
  using assms unfolding converse_def by auto

lemma mem_converseE [elim!]:
  assumes "p \<in> converse R"
  obtains x y where "p = \<langle>y, x\<rangle>" "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding converse_def uncurry_def by (auto)

lemma converse_pairs_eq [simp, intro!]: "converse (A \<times> B) = B \<times> A"
  by auto

lemma converse_empty_eq [simp, intro!]: "converse {} = {}"
  by auto

lemma dom_converse_eq_rng [simp]: "dom (converse R) = rng R"
  by auto

lemma rng_converse_eq_dom [simp]: "rng (converse R) = dom R"
  by auto

lemma converse_converse_eq: "converse (converse R) = {p \<in> R | \<exists>x y. p = \<langle>x, y\<rangle>}"
  by auto


text \<open>Diagonal of a set\<close>

definition "diag A \<equiv> {\<langle>a, a\<rangle> | a \<in> A}"

lemma mem_diagI [intro!]: "a \<in> A \<Longrightarrow> \<langle>a, a\<rangle> \<in> diag A"
  unfolding diag_def by auto

lemma mem_diagE [elim!]:
  assumes "p \<in> diag A"
  obtains a where "a \<in> A" "p = \<langle>a, a\<rangle>"
  using assms unfolding diag_def by auto


text \<open>Composition\<close>

definition "comp S R \<equiv> {p \<in> dom R \<times> rng S | \<exists>z. \<langle>fst p, z\<rangle> \<in> R \<and> \<langle>z, snd p\<rangle> \<in> S}"

bundle hotg_comp_syntax begin notation comp (infixr "\<circ>" 60) end
bundle no_hotg_comp_syntax begin no_notation comp (infixr "\<circ>" 60) end
unbundle hotg_comp_syntax

lemma mem_compI [intro!]:
  assumes "\<langle>x, y\<rangle> \<in> R"
  and "\<langle>y, z\<rangle> \<in> S"
  shows "\<langle>x, z\<rangle> \<in> S \<circ> R"
  using assms unfolding comp_def by auto

lemma mem_compE [elim!]:
  assumes "p \<in> S \<circ> R"
  obtains x y z where "\<langle>x, y\<rangle> \<in> R" "\<langle>y, z\<rangle> \<in> S" "p = \<langle>x, z\<rangle>"
  using assms unfolding comp_def by auto

lemma dep_pairs_comp_pairs_eq:
  "((\<Sum>x \<in> B. (C x)) \<circ> (A \<times> B)) = A \<times> (\<Union>x \<in> B. (C x))"
  by auto

lemma comp_assoc [simp]: "T \<circ> S \<circ> R = (T \<circ> S) \<circ> R"
  by auto

context
  fixes P :: "set \<Rightarrow> bool"
begin

lemma injective_compI:
  assumes "injective (rng R \<inter> dom S) R"
  and "injective P S"
  shows "injective P (S \<circ> R)"
  using assms by (auto dest: injectiveD)

lemma right_unique_compI:
  assumes "right_unique P R"
  and "right_unique (rng (R\<restriction>P) \<inter> dom S) S"
  shows "right_unique P (S \<circ> R)"
  using assms by (auto dest: right_uniqueD)

lemma left_total_compI:
  assumes "left_total P R"
  and "left_total (rng (R\<restriction>P)) S"
  shows "left_total P (S \<circ> R)"
  using assms by (intro left_totalI) auto

lemma surjective_compI:
  assumes "surjective (dom S) R"
  and "surjective P S"
  shows "surjective P (S \<circ> R)"
proof
  fix y assume "P y"
  then obtain x where "\<langle>x, y\<rangle> \<in> S" using assms(2) by auto
  moreover then have "x \<in> dom S" by auto
  moreover then obtain z where "\<langle>z, x\<rangle> \<in> R" using assms(1) by auto
  ultimately show "\<exists>x. \<langle>x, y\<rangle> \<in> S \<circ> R" by blast
qed

end

end
