theory Binary_Relations_Base
  imports LFunctions
begin

subsection \<open>Basic Functions\<close>

definition "rel_comp R S x y \<equiv> \<exists>z. R x z \<and> S z y"

bundle notation_rel_comp begin notation rel_comp (infixl "\<circ>\<circ>" 55) end
bundle no_notation_rel_comp begin no_notation rel_comp (infixl "\<circ>\<circ>" 55) end
unbundle notation_rel_comp

lemma rel_compI: "\<lbrakk>R x y; S y z\<rbrakk> \<Longrightarrow> (R \<circ>\<circ> S) x z"
  unfolding rel_comp_def by blast

lemma rel_compE:
  assumes "(R \<circ>\<circ> S) x y"
  obtains z where "R x z" "S z y"
  using assms unfolding rel_comp_def by blast

lemma rel_comp_assoc: "R \<circ>\<circ> (S \<circ>\<circ> T) = (R \<circ>\<circ> S) \<circ>\<circ> T"
  by (intro ext) (blast elim: rel_compE intro: rel_compI)

definition rel_inv :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  where "rel_inv R x y \<equiv> R y x"

lemma rel_invI: "R x y \<Longrightarrow> rel_inv R y x"
  unfolding rel_inv_def .

lemma rel_invD:
  assumes "rel_inv R x y"
  shows "R y x"
  using assms unfolding rel_inv_def .

lemma rel_inv_iff_rel: "rel_inv R x y \<longleftrightarrow> R y x"
  using rel_invI rel_invD by (intro iffI)

lemma rel_inv_comp_eq: "rel_inv (R \<circ>\<circ> S) = rel_inv S \<circ>\<circ> rel_inv R"
  by (intro ext) (blast intro: rel_invI rel_compI dest: rel_invD elim: rel_compE)

lemma rel_inv_rel_inv_eq_self: "rel_inv (rel_inv R) = R"
  by (intro ext) (blast intro: rel_invI dest: rel_invD)

lemma eq_if_rel_inv_eq: "rel_inv R = rel_inv S \<Longrightarrow> R = S"
  by (intro ext, (drule fun_cong)+) (blast dest: rel_invD intro: rel_invI)

definition in_dom :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  where "in_dom R x \<equiv> \<exists>y. R x y"

lemma in_domI: "R x y \<Longrightarrow> in_dom R x"
  unfolding in_dom_def by blast

lemma in_domE:
  assumes "in_dom R x"
  obtains y where " R x y"
  using assms unfolding in_dom_def by blast

lemma in_dom_if_in_dom_rel_comp:
  assumes "in_dom (R \<circ>\<circ> S) x"
  shows "in_dom R x"
  using assms by (blast elim: in_domE rel_compE intro: in_domI)

definition in_codom :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> bool"
  where "in_codom R y \<equiv> \<exists>x. R x y"

lemma in_codomI: "R x y \<Longrightarrow> in_codom R y"
  unfolding in_codom_def by blast

lemma in_codomE:
  assumes "in_codom R y"
  obtains x where " R x y"
  using assms unfolding in_codom_def by blast

lemma in_codom_if_in_codom_rel_comp:
  assumes "in_codom (R \<circ>\<circ> S) y"
  shows "in_codom S y"
  using assms by (blast elim: in_codomE rel_compE intro: in_codomI)

lemma in_codom_rel_inv_iff_in_dom: "in_codom (rel_inv R) x \<longleftrightarrow> in_dom R x"
  by (blast intro: in_codomI in_domI rel_invI elim!: in_domE in_codomE dest: rel_invD)

lemma in_dom_rel_inv_iff_in_codom: "in_dom (rel_inv R) y \<longleftrightarrow> in_codom R y"
proof -
  have "in_codom R y \<longleftrightarrow> in_codom (rel_inv (rel_inv R)) y"
    by (subst rel_inv_rel_inv_eq_self, rule refl)
  then show ?thesis using in_codom_rel_inv_iff_in_dom[symmetric] by simp
qed

consts restrict :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  restrict_pred \<equiv> "restrict :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
begin
  definition "restrict_pred R P x y \<equiv> P x \<and> R x y"
end

bundle restrict_syntax begin notation restrict ("_\<restriction>_" [50, 1000]) end
bundle no_restrict_syntax begin no_notation restrict ("_\<restriction>_") end
unbundle restrict_syntax

lemma restrictI:
  assumes "R x y"
  and "P x"
  shows "R\<restriction>P x y"
  using assms unfolding restrict_pred_def by blast

lemma restrictE:
  assumes "R\<restriction>P x y"
  obtains "P x" "R x y"
  using assms unfolding restrict_pred_def by blast

lemma in_dom_restrictI:
  assumes "R x y"
  and "P x"
  shows "in_dom (R\<restriction>P) x"
  using assms by (intro in_domI restrictI)

lemma in_dom_restrict_if_in_dom:
  assumes "in_dom R x"
  and "P x"
  shows "in_dom (R\<restriction>P) x"
  using assms by (elim in_domE, intro in_dom_restrictI)

lemma in_dom_restrictE:
  assumes "in_dom (R\<restriction>P) x"
  obtains y where "P x" "R x y"
  using assms by (elim in_domE restrictE)

lemma in_codom_restrictI:
  assumes "R x y"
  and "P x"
  shows "in_codom (R\<restriction>P) y"
  using assms by (intro in_codomI restrictI)

lemma in_codom_restrictE:
  assumes "in_codom (R\<restriction>P) y"
  obtains x where "P x" "R x y"
  using assms by (elim in_codomE restrictE)


subsection \<open>Basic Properties\<close>

consts rel_injective_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"

overloading
  rel_injective_on_pred \<equiv> "rel_injective_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "rel_injective_on_pred P R \<equiv> \<forall>x x' y. P x \<longrightarrow> P x' \<longrightarrow> R x y \<longrightarrow> R x' y \<longrightarrow> x = x'"
end

lemma rel_injective_onI:
  assumes "\<And>x x' y. P x \<Longrightarrow> P x' \<Longrightarrow> R x y \<Longrightarrow> R x' y \<Longrightarrow> x = x'"
  shows "rel_injective_on P R"
  unfolding rel_injective_on_pred_def using assms by blast

lemma rel_injective_onD:
  assumes "rel_injective_on P R"
  and "P x" "P x'"
  and "R x y" "R x' y"
  shows "x = x'"
  using assms unfolding rel_injective_on_pred_def by blast

definition "rel_injective (R :: 'a \<Rightarrow> _) \<equiv> rel_injective_on (\<lambda>x :: 'a. True) R"

lemma rel_injective_eq_rel_injective_on:
  "rel_injective (R :: 'a \<Rightarrow> _) = rel_injective_on (\<lambda>x :: 'a. True) R"
  unfolding rel_injective_def ..

lemma rel_injectiveI:
  assumes "\<And>x x' y. R x y \<Longrightarrow> R x' y \<Longrightarrow> x = x'"
  shows "rel_injective R"
  unfolding rel_injective_eq_rel_injective_on using assms by (intro rel_injective_onI)

lemma rel_injectiveD:
  assumes "rel_injective R"
  and "R x y" "R x' y"
  shows "x = x'"
  using assms unfolding rel_injective_eq_rel_injective_on by (blast dest: rel_injective_onD)

lemma rel_injective_on_if_rel_injective:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "rel_injective R"
  shows "rel_injective_on P R"
  using assms by (intro rel_injective_onI) (blast dest: rel_injectiveD)

consts right_unique_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"

overloading
  right_unique_on_pred \<equiv> "right_unique_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "right_unique_on_pred P R \<equiv> \<forall>x y y'. P x \<longrightarrow> R x y \<longrightarrow> R x y' \<longrightarrow> y = y'"
end

lemma right_unique_onI:
  assumes "\<And>x y y'. P x \<Longrightarrow> R x y \<Longrightarrow> R x y' \<Longrightarrow> y = y'"
  shows "right_unique_on P R"
  using assms unfolding right_unique_on_pred_def by blast

lemma right_unique_onD:
  assumes "right_unique_on P R"
  and "P x"
  and "R x y" "R x y'"
  shows "y = y'"
  using assms unfolding right_unique_on_pred_def by blast

definition "right_unique (R :: 'a \<Rightarrow> _) \<equiv> right_unique_on (\<lambda>x :: 'a. True) R"

lemma right_unique_eq_right_unique_on:
  "right_unique (R :: 'a \<Rightarrow> _) = right_unique_on (\<lambda>x :: 'a. True) R"
  unfolding right_unique_def ..

lemma right_uniqueI:
  assumes "\<And>x y y'. R x y \<Longrightarrow> R x y' \<Longrightarrow> y = y'"
  shows "right_unique R"
  unfolding right_unique_eq_right_unique_on using assms by (intro right_unique_onI)

lemma right_uniqueD:
  assumes "right_unique R"
  and "R x y" "R x y'"
  shows "y = y'"
  using assms unfolding right_unique_eq_right_unique_on
  by (blast dest: right_unique_onD)

lemma right_unique_on_if_right_unique:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "right_unique R"
  shows "right_unique_on P R"
  using assms by (intro right_unique_onI) (blast dest: right_uniqueD)

consts left_total_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"

overloading
  left_total_on_pred \<equiv> "left_total_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "left_total_on_pred P R \<equiv> \<forall>x. P x \<longrightarrow> in_dom R x"
end

lemma left_total_onI:
  assumes "\<And>x. P x \<Longrightarrow> in_dom R x"
  shows "left_total_on P R"
  unfolding left_total_on_pred_def using assms by blast

lemma left_total_onE:
  assumes "left_total_on P R"
  and "P x"
  obtains y where "R x y"
  using assms unfolding left_total_on_pred_def by (blast elim: in_domE)

lemma in_dom_if_left_total_on:
  assumes "left_total_on P R"
  and "P x"
  shows "in_dom R x"
  using assms by (blast intro: in_domI elim: left_total_onE)

definition "left_total (R :: 'a \<Rightarrow> _) \<equiv> left_total_on (\<lambda>x :: 'a. True) R"

lemma left_total_eq_left_total_on:
  "left_total (R :: 'a \<Rightarrow> _) = left_total_on (\<lambda>x :: 'a. True) R"
  unfolding left_total_def ..

lemma left_totalI:
  assumes "\<And>x. in_dom R x"
  shows "left_total R"
  unfolding left_total_eq_left_total_on using assms by (intro left_total_onI)

lemma left_totalE:
  assumes "left_total R"
  obtains y where "R x y"
  using assms unfolding left_total_eq_left_total_on by (blast elim: left_total_onE)

lemma in_dom_if_left_total:
  assumes "left_total R"
  shows "in_dom R x"
  using assms by (blast intro: in_domI elim: left_totalE)

lemma left_total_on_if_left_total:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "left_total R"
  shows "left_total_on P R"
  using assms by (intro left_total_onI) (blast dest: in_dom_if_left_total)

consts rel_surjective_at :: "'a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"

overloading
  rel_surjective_at_pred \<equiv> "rel_surjective_at :: ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "rel_surjective_at_pred P R \<equiv> \<forall>y. P y \<longrightarrow> in_codom R y"
end

lemma rel_surjective_atI:
  assumes "\<And>y. P y \<Longrightarrow> in_codom R y"
  shows "rel_surjective_at P R"
  unfolding rel_surjective_at_pred_def using assms by blast

lemma rel_surjective_atE:
  assumes "rel_surjective_at P R"
  and "P y"
  obtains x where "R x y"
  using assms unfolding rel_surjective_at_pred_def by (blast elim: in_codomE)

lemma in_codom_if_rel_surjective_at_on:
  assumes "rel_surjective_at P R"
  and "P y"
  shows "in_codom R y"
  using assms by (blast intro: in_codomI elim: rel_surjective_atE)

definition "rel_surjective (R :: _ \<Rightarrow> 'a \<Rightarrow> _) \<equiv> rel_surjective_at (\<lambda>x :: 'a. True) R"

lemma rel_surjective_eq_rel_surjective_at:
  "rel_surjective (R :: _ \<Rightarrow> 'a \<Rightarrow> _) = rel_surjective_at (\<lambda>x :: 'a. True) R"
  unfolding rel_surjective_def ..

lemma rel_surjectiveI:
  assumes "\<And>y. in_codom R y"
  shows "rel_surjective R"
  unfolding rel_surjective_eq_rel_surjective_at using assms by (intro rel_surjective_atI)

lemma rel_surjectiveE:
  assumes "rel_surjective R"
  obtains x where "R x y"
  using assms unfolding rel_surjective_eq_rel_surjective_at
  by (blast elim: rel_surjective_atE)

lemma in_codom_if_rel_surjective_at:
  assumes "rel_surjective R"
  shows "in_codom R y"
  using assms by (blast intro: in_codomI elim: rel_surjectiveE)

lemma rel_surjective_at_if_surjective:
  fixes P :: "'a \<Rightarrow> bool" and R :: "_ \<Rightarrow> 'a \<Rightarrow> _"
  assumes "rel_surjective R"
  shows "rel_surjective_at P R"
  using assms by (intro rel_surjective_atI) (blast dest: in_codom_if_rel_surjective_at)

consts reflexive_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"

overloading
  reflexive_on_pred \<equiv> "reflexive_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "reflexive_on_pred P R \<equiv> \<forall>x. P x \<longrightarrow> R x x"
end

lemma reflexive_onI:
  assumes "\<And>x. P x \<Longrightarrow> R x x"
  shows "reflexive_on P R"
  using assms unfolding reflexive_on_pred_def by blast

lemma reflexive_onD:
  assumes "reflexive_on P R"
  and "P x"
  shows "R x x"
  using assms unfolding reflexive_on_pred_def by blast

definition "reflexive (R :: 'a \<Rightarrow> _) \<equiv> reflexive_on (\<lambda>x :: 'a. True) R"

lemma reflexive_eq_reflexive_on:
  "reflexive (R :: 'a \<Rightarrow> _) = reflexive_on (\<lambda>x :: 'a. True) R"
  unfolding reflexive_def ..

lemma reflexiveI:
  assumes "\<And>x. R x x"
  shows "reflexive R"
  unfolding reflexive_eq_reflexive_on using assms by (intro reflexive_onI)

lemma reflexiveD:
  assumes "reflexive R"
  shows "R x x"
  using assms unfolding reflexive_eq_reflexive_on by (blast dest: reflexive_onD)

lemma reflexive_on_if_reflexive:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "reflexive R"
  shows "reflexive_on P R"
  using assms by (intro reflexive_onI) (blast dest: reflexiveD)

consts irreflexive_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"

overloading
  irreflexive_on_pred \<equiv> "irreflexive_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "irreflexive_on_pred P R \<equiv> \<forall>x. P x \<longrightarrow> \<not>(R x x)"
end

lemma irreflexive_onI:
  assumes "\<And>x. P x \<Longrightarrow> \<not>(R x x)"
  shows "irreflexive_on P R"
  using assms unfolding irreflexive_on_pred_def by blast

lemma irreflexive_onD:
  assumes "irreflexive_on P R"
  and "P x"
  shows "\<not>(R x x)"
  using assms unfolding irreflexive_on_pred_def by blast

definition "irreflexive (R :: 'a \<Rightarrow> _) \<equiv> irreflexive_on (\<lambda>x :: 'a. True) R"

lemma irreflexive_eq_irreflexive_on:
  "irreflexive (R :: 'a \<Rightarrow> _) = irreflexive_on (\<lambda>x :: 'a. True) R"
  unfolding irreflexive_def ..

lemma irreflexiveI:
  assumes "\<And>x. \<not>(R x x)"
  shows "irreflexive R"
  unfolding irreflexive_eq_irreflexive_on using assms by (intro irreflexive_onI)

lemma irreflexiveD:
  assumes "irreflexive R"
  shows "\<not>(R x x)"
  using assms unfolding irreflexive_eq_irreflexive_on by (blast dest: irreflexive_onD)

lemma irreflexive_on_if_irreflexive:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "irreflexive R"
  shows "irreflexive_on P R"
  using assms by (intro irreflexive_onI) (blast dest: irreflexiveD)

consts symmetric_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"

overloading
  symmetric_on_pred \<equiv> "symmetric_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "symmetric_on_pred P R \<equiv> \<forall>x y. P x \<longrightarrow> P y \<longrightarrow> R x y \<longrightarrow> R y x"
end

lemma symmetric_onI:
  assumes "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> R x y \<Longrightarrow> R y x"
  shows "symmetric_on P R"
  unfolding symmetric_on_pred_def using assms by blast

lemma symmetric_onD:
  assumes "symmetric_on P R"
  and "P x" "P y"
  and "R x y"
  shows "R y x"
  using assms unfolding symmetric_on_pred_def by blast

definition "symmetric (R :: 'a \<Rightarrow> _) \<equiv> symmetric_on (\<lambda>x :: 'a. True) R"

lemma symmetric_eq_symmetric_on:
  "symmetric (R :: 'a \<Rightarrow> _) = symmetric_on (\<lambda>x :: 'a. True) R"
  unfolding symmetric_def ..

lemma symmetricI:
  assumes "\<And>x y. R x y \<Longrightarrow> R y x"
  shows "symmetric R"
  unfolding symmetric_eq_symmetric_on using assms by (intro symmetric_onI)

lemma symmetricD:
  assumes "symmetric R"
  and "R x y"
  shows "R y x"
  using assms unfolding symmetric_eq_symmetric_on by (blast dest: symmetric_onD)

lemma symmetric_on_if_symmetric:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "symmetric R"
  shows "symmetric_on P R"
  using assms by (intro symmetric_onI) (blast dest: symmetricD)

lemma rel_inv_eq_self_if_symmetric:
  assumes "symmetric R"
  shows "rel_inv R = R"
  using assms by (blast intro: rel_invI dest: rel_invD symmetricD)

consts antisymmetric_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"

overloading
  antisymmetric_on_pred \<equiv> "antisymmetric_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "antisymmetric_on_pred P R \<equiv> \<forall>x y. P x \<longrightarrow> P y \<longrightarrow> R x y \<longrightarrow> R y x \<longrightarrow> x = y"
end

lemma antisymmetric_onI:
  assumes "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> R x y \<Longrightarrow> R y x \<Longrightarrow> x = y"
  shows "antisymmetric_on P R"
  unfolding antisymmetric_on_pred_def using assms by blast

lemma antisymmetric_onD:
  assumes "antisymmetric_on P R"
  and "P x" "P y"
  and "R x y" "R y x"
  shows "x = y"
  using assms unfolding antisymmetric_on_pred_def by blast

definition "antisymmetric (R :: 'a \<Rightarrow> _) \<equiv> antisymmetric_on (\<lambda>x :: 'a. True) R"

lemma antisymmetric_eq_antisymmetric_on:
  "antisymmetric (R :: 'a \<Rightarrow> _) = antisymmetric_on (\<lambda>x :: 'a. True) R"
  unfolding antisymmetric_def ..

lemma antisymmetricI:
  assumes "\<And>x y. R x y \<Longrightarrow> R y x \<Longrightarrow> x = y"
  shows "antisymmetric R"
  unfolding antisymmetric_eq_antisymmetric_on using assms
  by (intro antisymmetric_onI)

lemma antisymmetricD:
  assumes "antisymmetric R"
  and "R x y" "R y x"
  shows "x = y"
  using assms unfolding antisymmetric_eq_antisymmetric_on
  by (blast dest: antisymmetric_onD)

lemma antisymmetric_on_if_antisymmetric:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "antisymmetric R"
  shows "antisymmetric_on P R"
  using assms by (intro antisymmetric_onI) (blast dest: antisymmetricD)

consts transitive_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"

overloading
  transitive_on_pred \<equiv> "transitive_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "transitive_on_pred P R \<equiv> \<forall>x y z. P x \<longrightarrow> P y \<longrightarrow> P z \<longrightarrow> R x y \<longrightarrow> R y z \<longrightarrow> R x z"
end

lemma transitive_onI:
  assumes "\<And>x y z. P x \<Longrightarrow> P y \<Longrightarrow> P z \<Longrightarrow> R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  shows "transitive_on P R"
  unfolding transitive_on_pred_def using assms by blast

lemma transitive_onD:
  assumes "transitive_on P R"
  and "P x" "P y" "P z"
  and "R x y" "R y z"
  shows "R x z"
  using assms unfolding transitive_on_pred_def by blast

definition "transitive (R :: 'a \<Rightarrow> _) \<equiv> transitive_on (\<lambda>x :: 'a. True) R"

lemma transitive_eq_transitive_on:
  "transitive (R :: 'a \<Rightarrow> _) = transitive_on (\<lambda>x :: 'a. True) R"
  unfolding transitive_def ..

lemma transitiveI:
  assumes "\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  shows "transitive R"
  unfolding transitive_eq_transitive_on using assms by (intro transitive_onI)

lemma transitiveD:
  assumes "transitive R"
  and "R x y" "R y z"
  shows "R x z"
  using assms unfolding transitive_eq_transitive_on by (blast dest: transitive_onD)

lemma transitive_on_if_transitive:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "transitive R"
  shows "transitive_on P R"
  using assms by (intro transitive_onI) (blast dest: transitiveD)

definition "partial_equivalence_on P R \<equiv> symmetric_on P R \<and> transitive_on P R"

lemma partial_equivalence_onI:
  assumes "symmetric_on P R"
  and "transitive_on P R"
  shows "partial_equivalence_on P R"
  unfolding partial_equivalence_on_def using assms by blast

lemma partial_equivalence_onE:
  assumes "partial_equivalence_on P R"
  obtains "symmetric_on P R" "transitive_on P R"
  using assms unfolding partial_equivalence_on_def by blast

definition "partial_equivalence (R :: 'a \<Rightarrow> _) \<equiv> partial_equivalence_on (\<lambda>x :: 'a. True) R"

lemma partial_equivalence_eq_partial_equivalence_on:
  "partial_equivalence (R :: 'a \<Rightarrow> _) = partial_equivalence_on (\<lambda>x :: 'a. True) R"
  unfolding partial_equivalence_def ..

lemma partial_equivalenceI:
  assumes "symmetric R"
  and "transitive R"
  shows "partial_equivalence R"
  unfolding partial_equivalence_eq_partial_equivalence_on using assms
  by (intro partial_equivalence_onI symmetric_on_if_symmetric transitive_on_if_transitive)

lemma partial_equivalenceE:
  assumes "partial_equivalence R"
  obtains "symmetric R" "transitive R"
  using assms unfolding partial_equivalence_eq_partial_equivalence_on
  by (blast intro: symmetricI transitiveI dest: symmetric_onD transitive_onD
    elim: partial_equivalence_onE)

lemma partial_equivalence_on_if_partial_equivalence:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "partial_equivalence R"
  shows "partial_equivalence_on P R"
  using assms
  by (elim partial_equivalenceE, intro partial_equivalence_onI)
    (blast intro: symmetric_on_if_symmetric transitive_on_if_transitive)+

lemma rel_comp_self_eq_self_if_partial_equivalence:
  assumes "partial_equivalence R"
  shows "R \<circ>\<circ> R = R"
  using assms
  by (intro ext) (blast elim: partial_equivalenceE rel_compE intro: rel_compI
    dest: transitiveD symmetricD)


subsubsection \<open>Instantiations\<close>

lemma right_unique_eq: "right_unique (=)"
  by (rule right_uniqueI) blast

lemma symmetric_eq: "symmetric (=)"
  by (rule symmetricI) (rule sym)

lemma transitive_eq: "transitive (=)"
  by (rule transitiveI) (rule trans)

lemma partial_equivalence_eq: "partial_equivalence (=)"
  using symmetric_eq transitive_eq
  by (rule partial_equivalenceI)


end