\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Basic Setup\<close>
theory Set_Extensions_Base
  imports
    HOL_Basics.Restricted_Equality
    HOL_Basics.Functions_Injective
    HOL_Basics.Functions_Inverse
    HOTG.Set_Difference
    Sets
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

(*TODO: move somewhere else*)
overloading
  injective_on_set \<equiv> "injective_on :: set \<Rightarrow> (set \<Rightarrow> 'a) \<Rightarrow> bool"
  injective_on_type \<equiv> "injective_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
begin
  definition "injective_on_set A (f :: set \<Rightarrow> 'a) \<equiv> injective_on (mem_of A) f"
  definition "injective_on_type (T :: 'a type) (f :: 'a \<Rightarrow> 'b) \<equiv>
    injective_on (type_pred T) f"
end

lemma injective_on_set_eq_injective_on_pred [simp]:
  "(injective_on :: set \<Rightarrow> (set \<Rightarrow> 'a) \<Rightarrow> bool) A = injective_on (mem_of A)"
  unfolding injective_on_set_def by simp

lemma injective_on_set_iff_injective_on_pred [iff]:
  "injective_on (A :: set) (f :: set \<Rightarrow> 'a) \<longleftrightarrow> injective_on (mem_of A) f"
  by simp

lemma injective_on_type_eq_injective_on_pred [simp]:
  "(injective_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool) T = injective_on (type_pred T)"
  unfolding injective_on_type_def by simp

lemma injective_on_type_iff_injective_on_pred [iff]:
  "injective_on (T :: 'a type) (f :: 'a \<Rightarrow> 'b) \<longleftrightarrow> injective_on (type_pred T) f"
  by simp

overloading
  inverse_on_set \<equiv> "inverse_on :: set \<Rightarrow> (set \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> set) \<Rightarrow> bool"
  inverse_on_type \<equiv> "inverse_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "inverse_on_set A (f :: set \<Rightarrow> 'a) \<equiv> inverse_on (mem_of A) f"
  definition "inverse_on_type (T :: 'a type) (f :: 'a \<Rightarrow> 'b) \<equiv>
    inverse_on (type_pred T) f"
end

lemma inverse_on_set_eq_inverse_on_pred [simp]:
  "(inverse_on :: set \<Rightarrow> (set \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> set) \<Rightarrow> bool) A = inverse_on (mem_of A)"
  unfolding inverse_on_set_def by simp

lemma inverse_on_set_iff_inverse_on_pred [iff]:
  "inverse_on (A :: set) (f :: set \<Rightarrow> 'a) g \<longleftrightarrow> inverse_on (mem_of A) f g"
  by simp

lemma inverse_on_type_eq_inverse_on_pred [simp]:
  "(inverse_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool) T = inverse_on (type_pred T)"
  unfolding inverse_on_type_def by simp

lemma inverse_on_type_iff_inverse_on_pred [iff]:
  "inverse_on (T :: 'a type) (f :: 'a \<Rightarrow> 'b) g \<longleftrightarrow> inverse_on (type_pred T) f g"
  by simp

overloading
  restrict_left_set \<equiv> "restrict_left :: (set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow>
    (set \<Rightarrow> 'a \<Rightarrow> bool)"
  restrict_left_type \<equiv> "restrict_left :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a type \<Rightarrow>
    ('a \<Rightarrow> 'b \<Rightarrow> bool)"
begin
  definition "restrict_left_set (R :: set \<Rightarrow> _) (A :: set) \<equiv> R\<restriction>\<^bsub>mem_of A\<^esub>"
  definition "restrict_left_type (R :: 'a \<Rightarrow> _) (T :: 'a type) \<equiv> R\<restriction>\<^bsub>type_pred T\<^esub>"
end

lemma restrict_left_set_eq_restrict_left_pred [simp]:
  "restrict_left (R :: set \<Rightarrow> _) (A :: set) = R\<restriction>\<^bsub>mem_of A\<^esub>"
  unfolding restrict_left_set_def by simp

lemma restrict_left_set_iff_restrict_left_pred [iff]:
  "restrict_left (R :: set \<Rightarrow> _) (A :: set) x y \<longleftrightarrow> R\<restriction>\<^bsub>mem_of A\<^esub> x y"
  by simp

lemma restrict_left_type_eq_restrict_left_pred [simp]:
  "restrict_left (R :: 'a \<Rightarrow> _) (T :: 'a type) = R\<restriction>\<^bsub>type_pred T\<^esub>"
  unfolding restrict_left_type_def by simp

lemma restrict_left_type_iff_restrict_left_pred [iff]:
  "restrict_left (R :: 'a \<Rightarrow> _) (T :: 'a type) x y \<longleftrightarrow> R\<restriction>\<^bsub>type_pred T\<^esub> x y"
  by simp

overloading
  eq_restrict_set \<equiv> "eq_restrict :: set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
  eq_restrict_type \<equiv> "eq_restrict :: 'a type \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
begin
  definition "eq_restrict_set (A :: set) \<equiv> (=\<^bsub>mem_of A\<^esub> :: set \<Rightarrow> _)"
  definition "eq_restrict_type (T :: 'a type) \<equiv> (=\<^bsub>type_pred T\<^esub> :: 'a \<Rightarrow> _)"
end

lemma eq_restrict_set_eq_eq_restrict_pred [simp]:
  "(eq_restrict :: set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool) A = (=\<^bsub>mem_of A\<^esub>)"
  unfolding eq_restrict_set_def by simp

lemma eq_restrict_set_iff_eq_restrict_pred [iff]:
  "(eq_restrict :: set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool) A x y \<longleftrightarrow> x =\<^bsub>mem_of A\<^esub> y"
  by simp

lemma eq_restrict_type_eq_eq_restrict_pred [simp]:
  "(eq_restrict :: 'a type \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) T = (=\<^bsub>type_pred T\<^esub>)"
  unfolding eq_restrict_type_def by simp

lemma eq_restrict_type_iff_eq_restrict_pred [iff]:
  "(eq_restrict :: 'a type \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) T x y \<longleftrightarrow> x =\<^bsub>type_pred T\<^esub> y"
  by simp


locale set_extension =
  fixes Core Rep :: set and embed :: "set \<Rightarrow> set"
  assumes
    embed_type: "embed : Element Core \<Rightarrow> Element Rep" and
    embed_injective: "injective_on Core embed"
begin

definition "Abs \<equiv> Core \<union> {\<langle>Core, x\<rangle> | x \<in> (Rep \<setminus> {embed a | a \<in> Core})}"

lemma subset_Abs: "Core \<subseteq> Abs"
  unfolding Abs_def by auto

definition "l x \<equiv>
  if (\<exists>z \<in> Core. embed z = x) then (THE z. z \<in> Core \<and> embed z = x) else \<langle>Core, x\<rangle>"

definition "r y \<equiv> if y \<in> Core then embed y else snd y"

lemma left_type [type]: "l : Element Rep \<Rightarrow> Element Abs"
proof unfold_types
  fix x assume "x \<in> Rep"
  show "l x \<in> Abs"
  proof (cases "\<exists>z \<in> Core. embed z = x")
    case True
    then obtain z where z_props: "z \<in> Core \<and> embed z = x" by auto
    with embed_injective have uniq: "\<And>z'. z' \<in> Core \<and> embed z' = x \<Longrightarrow> z' = z"
      by (auto dest: injective_onD)
    with z_props have "(THE z. z \<in> Core \<and> embed z = x) = z" by (rule the_equality)
    with True have "l x = z" unfolding l_def by simp
    with z_props show "l x \<in> Abs" unfolding Abs_def by simp
  next
    case False
    with \<open>x \<in> Rep\<close> have "x \<in> Rep \<setminus> {embed a | a \<in> Core}" by auto
    with False show ?thesis unfolding Abs_def l_def by auto
  qed
qed

lemma right_type [type]: "r : Element Abs \<Rightarrow> Element Rep"
proof unfold_types
  fix y assume "y \<in> Abs"
  show "r y \<in> Rep"
  proof (cases "y \<in> Core")
    case True
    then have "r y = embed y" unfolding r_def by simp
    with embed_type True show ?thesis by simp
  next
    case False
    with \<open>y \<in> Abs\<close> obtain x where "x \<in> Rep" "y = \<langle>Core, x\<rangle>"
      unfolding Abs_def by auto
    with False have "r y = x" unfolding r_def by simp
    with \<open>x \<in> Rep\<close> show ?thesis by simp
  qed
qed

lemma inverse_on_Abs_right_left [iff]: "inverse_on Abs r l"
proof (subst inverse_on_set_iff_inverse_on_pred, rule inverse_onI)
  fix x assume "x \<in> Abs"
  then show "l (r x) = x"
  proof (cases "x \<in> Core")
    case True
    then have "l (r x) = l (embed x)" unfolding r_def by simp
    also from True have "... = (THE z. z \<in> Core \<and> embed z = embed x)"
      unfolding l_def by auto
    also have "... = x"
    proof (rule the_equality)
      show "x \<in> Core \<and> embed x = embed x" by simp
      from True embed_injective show "\<And>z. z \<in> Core \<and> embed z = embed x \<Longrightarrow> z = x"
        by (auto dest: injective_onD)
    qed
    finally show "l (r x) = x" .
  next
    case False
    with \<open>x \<in> Abs\<close> obtain y where y_props: "y \<in> Rep" "y \<notin> {embed a | a \<in> Core}"
      and x_eq: "x = \<langle>Core, y\<rangle>"
      unfolding Abs_def by auto
    from False have "l (r x) = l (snd x)" unfolding r_def by simp
    also from x_eq have "... = l y" by simp
    also from y_props have "... = \<langle>Core, y\<rangle>" unfolding l_def by auto
    also from x_eq have "... = x" ..
    finally show "l (r x) = x" .
  qed
qed

lemma inverse_on_Rep_left_right [iff]: "inverse_on Rep l r"
proof (subst inverse_on_set_iff_inverse_on_pred, rule inverse_onI)
  fix x assume "x \<in> Rep"
  then show "r (l x) = x"
  proof (cases "\<exists>z \<in> Core. embed z = x")
    case True
    then obtain z where z_props: "z \<in> Core \<and> embed z = x" by auto
    with True have "r (l x) = r (THE z. z \<in> Core \<and> embed z = x)"
      unfolding l_def by simp
    also have "... = r z"
    proof (subst the_equality)
      from z_props embed_injective show "\<And>z'. z' \<in> Core \<and> embed z' = x \<Longrightarrow> z' = z"
        by (auto dest: injective_onD)
    qed (auto intro!: z_props)
    also from z_props have "... = embed z" unfolding r_def by simp
    also from z_props have "... = x" by simp
    finally show "r (l x) = x" .
  next
    case False
    then have "r (l x) = r \<langle>Core, x\<rangle>" unfolding l_def by auto
    also have "... = x" unfolding r_def by simp
    finally show "r (l x) = x" .
  qed
qed


end


end
