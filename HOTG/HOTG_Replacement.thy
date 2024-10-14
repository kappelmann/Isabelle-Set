\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Larry Paulson"\<close>
section \<open>Replacement\<close>
theory HOTG_Replacement
  imports
    HOTG_Bounded_Quantifiers
    HOTG_Equality
    Transport.Functions_Injective
begin

open_bundle hotg_repl_syntax
begin
syntax "_repl" :: \<open>[set, pttrn, set] => set\<close> ("{_ |/ _ \<in> _}")
end
syntax_consts "_repl" \<rightleftharpoons> repl
translations
  "{y | x \<in> A}" \<rightleftharpoons> "CONST repl A (\<lambda>x. y)"

lemma app_mem_repl_if_mem [intro]: "a \<in> A \<Longrightarrow> f a \<in> {f x | x \<in> A}"
  by auto

lemma bex_eq_app_if_mem_repl: "b \<in> {f x | x \<in> A} \<Longrightarrow> \<exists>a : A. b = f a"
  by auto

lemma replE [elim!]:
  assumes "b \<in> {f x | x \<in> A}"
  obtains x where "x \<in> A" and "b = f x"
  using assms by (auto dest: bex_eq_app_if_mem_repl)

lemma repl_cong [cong]:
  "\<lbrakk>A = B; \<And>x. x \<in> B \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> {f x | x \<in> A} = {g x | x \<in> B}"
  by (rule eq_if_subset_if_subset) blast+

lemma repl_repl_eq_repl [simp]: "{g b | b \<in> {f a | a \<in> A}} = {g (f a) | a \<in> A}"
  by (rule eq_if_subset_if_subset) auto

lemma repl_eq_dom [simp]: "{x | x \<in> A} = A"
  by (rule eq_if_subset_if_subset) auto

lemma repl_eq_empty [simp]: "{f x | x \<in> {}} = {}"
  by (rule eq_if_subset_if_subset) auto

lemma repl_eq_empty_iff [iff]: "{f x | x \<in> A} = {} \<longleftrightarrow> A = {}"
  by auto

lemma repl_subset_repl_if_subset_dom [intro!]:
  "A \<subseteq> B \<Longrightarrow> {g y | y \<in> A} \<subseteq> {g y | y \<in> B}"
  by auto

lemma ball_repl_iff_ball [iff]: "(\<forall>x : {f x | x \<in> A}. P x) \<longleftrightarrow> (\<forall>x : A. P (f x))"
  by auto

lemma bex_repl_iff_bex [iff]: "(\<exists>x : {f x | x \<in> A}. P x) \<longleftrightarrow> (\<exists>x : A. P (f x))"
  by auto

lemma mono_subset_subset_repl: "((\<subseteq>) \<Rightarrow> (\<subseteq>)) (\<lambda>A. {f x | x \<in> A})"
  by auto


subsection \<open>Image\<close>

definition "image f A \<equiv> {f x | x \<in> A}"

lemma image_eq_repl [simp]: "image f A = repl A f"
  unfolding image_def by simp

lemma image_eq_repl_uhint [uhint]:
  assumes "f \<equiv> f'"
  and "A \<equiv> A'"
  shows "image f A = repl A' f'"
  using assms by simp

lemma injective_image_if_injective:
  assumes "injective f"
  shows "injective (image f)"
  using assms by (intro injectiveI eqI) (auto dest: injectiveD)

lemma injective_if_injective_image:
  assumes "injective (image f)"
  shows "injective f"
proof (rule injectiveI)
  fix X Y assume "f X = f Y"
  then have "image f {X | _ \<in> powerset {}} = image f {Y | _ \<in> powerset {}}" by simp
  with assms show "X = Y" by (blast dest: injectiveD)
qed

corollary injective_image_iff_injective [iff]: "injective (image f) \<longleftrightarrow> injective f"
  using injective_image_if_injective injective_if_injective_image by blast


end

