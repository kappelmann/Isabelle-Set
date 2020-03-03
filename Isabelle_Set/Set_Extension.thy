section \<open>Set extensions\<close>

theory Set_Extension
imports Function
begin

text \<open>
  This theory defines a definitional principle for set extensions.

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
  \<^item> There are functions \<open>Rep : element B' \<Rightarrow> element B\<close> and
    \<open>Abs : element B \<Rightarrow> element B'\<close> that are inverses of each other. In other
    words, there is a bijection between \<open>B\<close> and \<open>B'\<close>.

  While the underlying construction involves case distinctions, this is hidden
  under the surface of the bijection in the end, and will not get in the way
  when reasoning about the newly defined set. Primitive operations on \<open>B'\<close> will
  usually be defined by lifting them over from operations on \<open>B\<close>, in the same
  way as is done for type definitions in HOL.
\<close>

locale set_extension =
fixes 
  A B :: set
  and f :: "set \<Rightarrow> set"
assumes
 f_type: "f : element A \<Rightarrow> element B"
 and f_injective: "\<forall>x\<in>A. \<forall>y\<in>A. f x = f y \<longrightarrow> x = y"
begin

definition def :: set
  where "def = A \<union> {\<langle>A, x\<rangle> | x \<in> B \<setminus> {f a | a \<in> A}}"

definition Rep :: "set \<Rightarrow> set"
  where "Rep y = (if y \<in> A then f y else snd y)"

definition Abs :: "set \<Rightarrow> set"
  where "Abs x = (if (\<exists>z\<in>A. f z = x) then (THE z. z\<in>A \<and> f z = x) else \<langle>A, x\<rangle>)"

lemma Rep_type [type]: "Rep : element def \<Rightarrow> element B"
proof (rule Pi_typeI)
  fix y assume "y : element def"
  show "Rep y : element B"
  proof (cases "y \<in> A")
    case True
    then have "Rep y = f y" unfolding Rep_def by simp
    with f_type True show ?thesis by unfold_types
  next
    case False
    with `y : element def` obtain x where "x \<in> B" "y = \<langle>A, x\<rangle>"
      unfolding def_def by unfold_types auto
    then have "Rep y = x" unfolding Rep_def using False by simp
    with `x \<in> B` show ?thesis by unfold_types
  qed
qed

lemma Abs_type [type]: "Abs : element B \<Rightarrow> element def"
proof (rule Pi_typeI)
  fix x assume "x : element B"
  show "Abs x : element def"
  proof (cases "\<exists>z\<in>A. f z = x")
    case True then obtain z where z: "z \<in> A \<and> f z = x" by auto
    with f_injective
    have uniq: "\<And>z'. z'\<in>A \<and> f z' = x \<Longrightarrow> z' = z" by auto
    with z have "(THE z. z\<in>A \<and> f z = x) = z"
      by (rule the_equality)
    with True have "Abs x = z" unfolding Abs_def by simp
    with z have "Abs x \<in> def" unfolding def_def by auto
    then show ?thesis by unfold_types
  next
    case False
    with `x : element B` 
    have "x \<in> B \<setminus> Repl A f" by unfold_types auto
    then show ?thesis unfolding def_def Abs_def by unfold_types auto
  qed
qed    

lemma Rep_inverse [simp]:
  assumes "x : element def"
  shows "Abs (Rep x) = x"
proof (cases "x \<in> A")
  case True
  then have fx: "Rep x = f x" unfolding Rep_def by simp
  with `x \<in> A` have exists: "x\<in>A \<and> f x = f x" by simp
  with f_injective have unique: "\<And>z. z\<in>A \<and> f z = f x \<Longrightarrow> z = x" by force

  have "Abs (Rep x) = Abs (f x)" using `x \<in> A` by (simp add: fx)
  also from `x \<in> A` have "... = (THE z. z\<in>A \<and> f z = f x)" unfolding Abs_def by auto
  also from exists unique have "... = x" by (rule the_equality)
  finally show "Abs (Rep x) = x" .
next
  case False
  with assms obtain y where y: "y\<in>B" "y \<notin> Repl A f" and x_eq: "x = \<langle>A, y\<rangle>"
    unfolding def_def by unfold_types auto

  from `x \<notin> A` have "Abs (Rep x) = Abs (snd x)" by (simp add: Rep_def)
  also from x_eq have "... = Abs y" by auto
  also from y have "... = \<langle>A, y\<rangle>" unfolding Abs_def by auto
  also from x_eq have "... = x" ..
  finally show "Abs (Rep x) = x" .
qed

lemma Abs_inverse [simp]:
  assumes "x : element B"
  shows "Rep (Abs x) = x"
proof (cases "\<exists>z\<in>A. f z = x")
  case True then obtain z where z: "z \<in> A \<and> f z = x" by auto
  with f_injective
  have uniq: "\<And>z'. z'\<in>A \<and> f z' = x \<Longrightarrow> z' = z" by auto
  with z have "(THE z. z\<in>A \<and> f z = x) = z" by (rule the_equality)

  with True have "Rep (Abs x) = Rep z" unfolding Abs_def by simp
  also from z have "... = f z" unfolding Rep_def by simp
  also from z have "... = x" ..
  finally show "Rep (Abs x) = x" .
next  
  case False
  then have "Rep (Abs x) = Rep (\<langle>A, x\<rangle>)" unfolding Abs_def by simp
  also have "... = x" unfolding Rep_def by (simp add: opair_not_in_fst)
  finally show "Rep (Abs x) = x" .
qed

lemma extension_subset: "A \<subseteq> def"
  unfolding def_def by auto


end

end
