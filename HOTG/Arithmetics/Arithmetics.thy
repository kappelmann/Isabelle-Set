theory Arithmetics
  imports
    Union_Intersection
    Transport.HOL_Syntax_Bundles_Groups
begin

unbundle no_HOL_ascii_syntax

definition "image f A \<equiv> {f x | x \<in> A}"

lemma image_eq_repl [simp]: "image f A = {f x | x \<in> A}"
  unfolding image_def by simp

definition "fun_restrict f P x \<equiv> if P x then f x else undefined"

lemma fun_restrict_eq_if_True [simp]:
  assumes "P x"
  shows "fun_restrict f P x = f x"
  unfolding fun_restrict_def using assms by simp

lemma fun_restrict_eq_if_not [simp]:
  assumes "\<not>(P x)"
  shows "fun_restrict f P x = undefined"
  unfolding fun_restrict_def using assms by simp

axiomatization transrec :: "((set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a"
  where transrec_eq: "transrec f x = f (fun_restrict (transrec f) (mem_of x)) x"

definition "add X \<equiv> transrec (\<lambda>addX Y. X \<union> image addX Y)"

bundle hotg_add_syntax begin notation add (infixl "+" 65) end
bundle no_hotg_add_syntax begin no_notation add (infixl "+" 65) end
unbundle hotg_add_syntax
unbundle no_HOL_groups_syntax

lemma add_eq_union_image_add: "X + Y = X \<union> image ((+) X) Y"
  unfolding add_def by (simp add: transrec_eq)

definition "lift X \<equiv> image ((+) X)"

lemma lift_eq_image_add: "lift X = image ((+) X)"
  unfolding lift_def by simp

lemma add_eq_union_lift: "X + Y = X \<union> lift X Y"
  unfolding lift_eq_image_add by (subst add_eq_union_image_add) simp

lemma lift_union_distrib: "lift X (A \<union> B) = lift X A \<union> lift X B"
  by (auto simp: lift_eq_image_add)

end
