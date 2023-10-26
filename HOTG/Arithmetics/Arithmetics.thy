theory Arithmetics
  imports
    Union_Intersection
    Transport.HOL_Syntax_Bundles_Groups
    Axioms
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

lemma elem_zero_lift [simp]: "lift x {} = {}"
  unfolding lift_def by simp

lemma zero_add [simp]: " x + {} = x"
  unfolding add_eq_union_lift by simp

lemma one_lift: "lift x {{}} = {x}"
  unfolding lift_def by simp

definition "adduction x y \<equiv> x \<union> {y} "
(*priority number*)

lemma one_add_eq_adduction: "x + {{}} = x \<union> {x}"
  by(auto simp: add_eq_union_lift one_lift)

lemma lift_elem_add: " lift x {z} =  {x + z}"
  unfolding lift_def by simp

lemma lift_elem: "lift x {z} = {x \<union> lift x z}"
  by (auto simp:lift_elem_add  add_eq_union_lift)

lemma add_elem_subst: "X + {Y} = X \<union> {X + Y}"
  unfolding add_eq_union_lift by (auto simp: lift_elem)

lemma lift_elems: "lift x (y \<union> {z}) = lift x y \<union> {x \<union> lift x z}"
  unfolding lift_union_distrib by (auto simp: lift_elem)

lemma adduction_distributive: "x + (adduction y z) = adduction (x + y) (x + z)"
  unfolding adduction_def  add_eq_union_lift by (auto simp: lift_elems)


lemma zero_elem_lift: "{} + X = X"
proof (induct X rule: mem_induction)
  case (1 X)
  then show ?case sorry
qed

    

theorem assoc_add: "x + (y + z) = (x + y) +z"
proof-
  have"(x + y) + z = (x + y) \<union> (lift (x+y) z)"
    by (auto simp: add_eq_union_lift)
  then have"... = (x + y) \<union> {(x + y) + u | u \<in> z }"
    by (auto simp: lift_def)
  then have"... = x \<union> (lift x y) \<union> {(x + y) + u | u \<in> z }"
    by (auto simp:add_eq_union_lift)
  then have"... = x \<union> (lift x y) \<union> {x + (y + u) | u \<in> z }"
    sorry
    (*eps-induction is needed*)
  then have"... =  x \<union> (lift x y) \<union> {(y + u) | u \<in> z }"
    sorry
    (*by (auto simp: lift_union_distrib)*)
  then have"... = x \<union> lift x (y + z)"
    sorry
  then show ?thesis 
    sorry
qed



definition "TC \<equiv> transrec (\<lambda>f x. x \<union> \<Union>(image f x)) "

(*
definition plus_V :: "V \<Rightarrow> V \<Rightarrow> V"
  where "plus_V x \<equiv> transrec (\<lambda>f z. x \<squnion> set (f ` elts z))"
definition times_V :: "V \<Rightarrow> V \<Rightarrow> V"
  where "times_V x \<equiv> transrec (\<lambda>f y. \<Squnion> ((\<lambda>u. lift (f u) x) ` elts y))"
definition "add X \<equiv> transrec (\<lambda>addX Y. X \<union> image addX Y)"
*)

definition "mul X \<equiv> transrec (\<lambda>mulX Y. X \<union> image (add (image mulX Y)) X)"

bundle hotg_mul_syntax begin notation mul (infixl "*" 70) end
bundle no_hotg_mul_syntax begin no_notation add (infixl "*" 70) end
unbundle hotg_mul_syntax
unbundle no_HOL_groups_syntax

lemma mul_zero: "x * y = \<Union>{lift (x*u) x | u \<in> y}"
  sorry


end
