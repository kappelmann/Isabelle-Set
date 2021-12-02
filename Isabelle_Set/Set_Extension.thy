section \<open>Set extensions\<close>
theory Set_Extension
imports Functions
begin

text \<open>This theory defines a definitional principle for set extensions.

We assume that we have defined a set \<open>A\<close> (e.g., the naturals), for which we
want to construct an extension (e.g., the integers). A standard construction
could be to adjoin a sign or to use equivalence classes of pairs of naturals.
In any case, we cannot identify the integers with these constructions, since
then they would not contain the naturals (which are already defined and cannot
be changed).

This principle of set extensions solves this by plugging in the original set
into the new construction.

Formally, given
\<^item> A set \<open>A\<close>, which is supposed to stay fixed
\<^item> A set \<open>B\<close>, which is the new construction
\<^item> An injective function from \<open>A\<close> to \<open>B\<close>, which embeds the original set into
  the new one

we construct a set \<open>B'\<close>, such that
\<^item> \<open>A \<subseteq> B'\<close>
\<^item> There are functions \<open>Rep: Element B' \<Rightarrow> Element B\<close> and
  \<open>Abs: Element B \<Rightarrow> Element B'\<close> that are inverses of each other. In other
  words, there is a bijection between \<open>B\<close> and \<open>B'\<close>.

While the underlying construction involves case distinctions, this is hidden
under the surface of the bijection in the end, and will not get in the way
when reasoning about the newly defined set. Primitive operations on \<open>B'\<close> will
usually be defined by lifting them over from operations on \<open>B\<close>, in the same
way as is done for type definitions in HOL.\<close>

locale set_extension =
  fixes A B :: set and f :: "set \<Rightarrow> set"
  assumes
    f_type: "f : Element A \<Rightarrow> Element B" and
    f_injective: "\<forall>x \<in> A. \<forall>y \<in> A. f x = f y \<longrightarrow> x = y"
begin

definition "abs_image \<equiv> A \<union> {\<langle>A, x\<rangle> | x \<in> (B \<setminus> {f a | a \<in> A})}"

lemma subset_abs_image: "A \<subseteq> abs_image"
  unfolding abs_image_def by auto

definition "Rep y \<equiv> if y \<in> A then f y else snd y"

definition "Abs x \<equiv>
  if (\<exists>z \<in> A. f z = x) then (THE z. z \<in> A \<and> f z = x) else \<langle>A, x\<rangle>"

lemma Rep_type [type]: "Rep : Element abs_image \<Rightarrow> Element B"
proof unfold_types
  fix y assume "y \<in> abs_image"
  show "Rep y \<in> B"
  proof (cases "y \<in> A")
    case True
    then have "Rep y = f y" unfolding Rep_def by simp
    with f_type True show ?thesis by simp
  next
    case False
    with \<open>y \<in> abs_image\<close> obtain x where "x \<in> B" "y = \<langle>A, x\<rangle>"
      unfolding abs_image_def by auto
    with False have "Rep y = x" unfolding Rep_def by simp
    with \<open>x \<in> B\<close> show ?thesis by simp
  qed
qed

lemma Abs_type [type]: "Abs : Element B \<Rightarrow> Element abs_image"
proof unfold_types
  fix x assume "x \<in> B"
  show "Abs x \<in> abs_image"
  proof (cases "\<exists>z \<in> A. f z = x")
    case True
    then obtain z where z_props: "z \<in> A \<and> f z = x" by auto
    with f_injective have uniq: "\<And>z'. z' \<in> A \<and> f z' = x \<Longrightarrow> z' = z" by auto
    with z_props have "(THE z. z \<in> A \<and> f z = x) = z" by (rule the_equality)
    with True have "Abs x = z" unfolding Abs_def by simp
    with z_props show "Abs x \<in> abs_image" unfolding abs_image_def by simp
  next
    case False
    with \<open>x \<in> B\<close> have "x \<in> B \<setminus> {f a | a \<in> A}" by auto
    with False show ?thesis unfolding abs_image_def Abs_def by auto
  qed
qed

lemma Abs_Rep_inv [simp]:
  assumes "x \<in> abs_image"
  shows "Abs (Rep x) = x"
proof (cases "x \<in> A")
  case True
  then have "Abs (Rep x) = Abs (f x)" unfolding Rep_def by simp
  also from True have "... = (THE z. z \<in> A \<and> f z = f x)"
    unfolding Abs_def by auto
  also have "... = x"
  proof (rule the_equality)
    show "x \<in> A \<and> f x = f x" by simp
    from True f_injective show "\<And>z. z \<in> A \<and> f z = f x \<Longrightarrow> z = x" by blast
  qed
  finally show "Abs (Rep x) = x" .
next
  case False
  with assms obtain y where y_props: "y \<in> B" "y \<notin> {f a | a \<in> A}"
    and x_eq: "x = \<langle>A, y\<rangle>"
    unfolding abs_image_def by auto
  from False have "Abs (Rep x) = Abs (snd x)" unfolding Rep_def by simp
  also from x_eq have "... = Abs y" by simp
  also from y_props have "... = \<langle>A, y\<rangle>" unfolding Abs_def by auto
  also from x_eq have "... = x" ..
  finally show "Abs (Rep x) = x" .
qed

lemma Rep_Abs_inv [simp]: "Rep (Abs x) = x"
proof (cases "\<exists>z \<in> A. f z = x")
  case True
  then obtain z where z_props: "z \<in> A \<and> f z = x" by auto
  with True have "Rep (Abs x) = Rep (THE z. z \<in> A \<and> f z = x)"
    unfolding Abs_def by simp
  also have "... = Rep z"
  proof (subst the_equality)
    from z_props f_injective show "\<And>z'. z' \<in> A \<and> f z' = x \<Longrightarrow> z' = z" by auto
  qed (auto intro!: z_props)
  also from z_props have "... = f z" unfolding Rep_def by simp
  also from z_props have "... = x" by simp
  finally show "Rep (Abs x) = x" .
next
  case False
  then have "Rep (Abs x) = Rep \<langle>A, x\<rangle>" unfolding Abs_def by auto
  also have "... = x" unfolding Rep_def by simp
  finally show "Rep (Abs x) = x" .
qed

end


end
