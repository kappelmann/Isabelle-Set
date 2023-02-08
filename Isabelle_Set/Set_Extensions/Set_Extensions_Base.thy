\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Basic Setup\<close>
theory Set_Extensions_Base
  imports
    HOTG.Set_Difference
    Sets
    TFunctions
begin

text \<open>This theory defines a definitional principle for set extensions.

We assume that we have defined a set \<open>Core\<close> (e.g., the naturals), for which we
want to construct an extension (e.g., the integers). A standard construction
could be to adjoin a sign or to use equivalence classes of pairs of naturals.
In any case, we cannot identify the integers with these constructions, since
then they would not contain the naturals (which are already defined and cannot
be changed).

This principle of set extensions solves this by plugging in the original set
into the new construction.

Formally, given
\<^item> A set \<open>Core\<close>, which is supposed to stay fixed
\<^item> A set \<open>Rep\<close>, which is the new construction
\<^item> An injective function from \<open>Core\<close> to \<open>Rep\<close>, which embeds the original set into
  the new one

we construct a set \<open>Abs\<close>, such that
\<^item> @{term "Core \<subseteq> Abs"}
\<^item> There are functions @{prop "l : Element Rep \<Rightarrow> Element Abs"} and
  @{prop "r : Element Abs \<Rightarrow> Element Rep"} that are inverses of each other.
  In other words, there is a bijection between \<open>Rep\<close> and \<open>Abs\<close>.

While the underlying construction involves case distinctions, this is hidden
under the surface of the bijection in the end, and will not get in the way
when reasoning about the newly defined set. Primitive operations on \<open>Abs\<close> will
usually be transported from \<open>Rep\<close> using \<open>abs\<close>.\<close>

locale set_extension =
  fixes Core Rep :: set and embed :: "set \<Rightarrow> set"
  assumes
    embed_type [type]: "embed : Element Core \<Rightarrow> Element Rep" and
    embed_injective: "injective_on Core embed"
begin

definition "Abs \<equiv> Core \<union> {\<langle>Core, x\<rangle> | x \<in> (Rep \<setminus> {embed c | c \<in> Core})}"

lemma mem_AbsE:
  assumes "y \<in> Abs"
  obtains "y \<in> Core"
    | x where "x \<in> Rep" "x \<notin> {embed c | c \<in> Core}" "y = \<langle>Core, x\<rangle>"
  using assms unfolding Abs_def by auto

lemma Core_subset_Abs: "Core \<subseteq> Abs"
  unfolding Abs_def by auto

definition "l x \<equiv>
  if (\<exists>c \<in> Core. embed c = x) then (THE c. c \<in> Core \<and> embed c = x) else \<langle>Core, x\<rangle>"

lemma left_embed_eq_if_mem_Core [simp]:
  assumes "c \<in> Core"
  shows "l (embed c) = c"
proof -
  from assms embed_injective have "(THE c'. c' \<in> Core \<and> embed c' = embed c) = c"
    by (intro the_equality) (auto dest: injective_onD)
  with assms show ?thesis unfolding l_def by auto
qed

corollary left_embed_mem_Core_if_mem_Core [intro]:
  assumes "c \<in> Core"
  shows "l (embed c) \<in> Core"
  using assms by simp

lemma left_mem_CoreE [elim]:
  assumes "l x \<in> Core"
  obtains c where "c \<in> Core" "x = embed c"
  using assms unfolding l_def by (auto split: if_splits)

corollary left_mem_Core_iff: "l x \<in> Core \<longleftrightarrow> (\<exists>c \<in> Core. embed c = x)"
  by auto

lemma left_eq_pairI:
  assumes "\<And>c. c \<in> Core \<Longrightarrow> embed c \<noteq> x"
  shows "l x = \<langle>Core, x\<rangle>"
  unfolding l_def using assms by auto

definition "r y \<equiv> if y \<in> Core then embed y else snd y"

lemma right_eq_embed_if_mem_Core [simp]:
  assumes "c \<in> Core"
  shows "r c = embed c"
  unfolding r_def using assms by simp

lemma right_eq_snd [simp]:
  assumes "y \<notin> Core"
  shows "r y = snd y"
  using assms unfolding r_def by simp

lemma right_pair_Core_eq_snd [simp]: "r \<langle>Core, y\<rangle> = y"
  by simp

lemma left_type [type]: "l : Element Rep \<Rightarrow> Element Abs"
proof unfold_types
  fix x assume "x \<in> Rep"
  show "l x \<in> Abs"
  proof (cases "\<exists>c \<in> Core. x = embed c")
    case True
    with Core_subset_Abs show "l x \<in> Abs" by auto
  next
    case False
    then show ?thesis unfolding Abs_def l_def by auto
  qed
qed

lemma right_type [type]: "r : Element Abs \<Rightarrow> Element Rep"
  by unfold_types (auto elim: mem_AbsE)

lemma inverse_on_Abs_right_left: "inverse_on Abs r l"
proof (subst inverse_on_set_iff_inverse_on_pred, rule inverse_onI)
  fix y assume "y \<in> Abs"
  show "l (r y) = y"
  proof (cases "y \<in> Core")
    case False
    with \<open>y \<in> Abs\<close> obtain x where x_props: "x \<in> Rep" "x \<notin> {embed c | c \<in> Core}"
      and y_eq: "y = \<langle>Core, x\<rangle>" by (blast elim: mem_AbsE)
    with False have "l (r y) = l x" by simp
    also from x_props have "... = \<langle>Core, x\<rangle>" by (intro left_eq_pairI) blast
    also from y_eq have "... = y" ..
    finally show "l (r y) = y" .
  qed simp
qed

lemma inverse_on_Rep_left_right: "inverse_on Rep l r"
proof (subst inverse_on_set_iff_inverse_on_pred, rule inverse_onI)
  fix x assume "x \<in> Rep"
  show "r (l x) = x"
  proof (cases "\<exists>c \<in> Core. x = embed c")
    case False
    then have "r (l x) = r \<langle>Core, x\<rangle>" unfolding l_def by auto
    also have "... = x" by simp
    finally show "r (l x) = x" .
  qed auto
qed

end


end
