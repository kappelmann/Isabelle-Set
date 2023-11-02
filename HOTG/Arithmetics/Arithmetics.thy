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
  where transrec_eq: "transrec f X = f (fun_restrict (transrec f) (mem_of X)) X"

definition "add X \<equiv> transrec (\<lambda>addX Y. X \<union> image addX Y)"

bundle hotg_add_syntax begin notation add (infixl "+" 65) end
bundle no_hotg_add_syntax begin no_notation add (infixl "+" 65) end
unbundle hotg_add_syntax
unbundle no_HOL_groups_syntax

lemma add_eq_union_image_add: "X + Y = X \<union> image ((+) X) Y"
  unfolding add_def by (simp add: transrec_eq)

(*can not use add_eq_union_image_add directly, it will get into a loop*)
lemma add_eq_union_image_add_copy: "X + Y = X \<union> image ((+) X) Y"
  sorry
 (* by (simp add:add_eq_union_image_add)*)

definition "lift X \<equiv> image ((+) X)"

lemma lift_eq_image_add: "lift X = image ((+) X)"
  unfolding lift_def by simp

lemma add_eq_union_lift: "X + Y = X \<union> lift X Y"
  unfolding lift_eq_image_add by (subst add_eq_union_image_add) simp

text\<open>Lemma 3.2\<close>
lemma lift_bin_union_distrib: "lift X (A \<union> B) = lift X A \<union> lift X B"
  by (auto simp: lift_eq_image_add)

lemma lift_union_distrib: "lift x (\<Union> Y) = \<Union> (image (lift x) Y)"
  by (auto simp: lift_eq_image_add)

lemma add_Sup_distrib: "Y \<noteq> {} \<Longrightarrow> x + {f y | y \<in> Y} =  {x + f y | y \<in> Y}"
  sorry

lemma lift_zero_right [simp]: "lift X {} = {}"
  by (auto simp: lift_eq_image_add)

lemma add_zero_right [simp]: "x + {} = x"
  unfolding add_eq_union_lift by simp

lemma lift_one_right [simp]: "lift x {{}} = {x}"
  unfolding lift_def by simp

definition "adduct x y \<equiv> x \<union> {y}"

lemma adduct_eq: "adduct x y = x \<union> {y}"
  by (simp add: adduct_def)

lemma add_one_eq_adduct: "x + {{}} = adduct x x"
  by (simp add: add_eq_union_lift adduct_eq)

lemma lift_elem_add: "lift x {z} = {x + z}"
  unfolding lift_def by simp

lemma lift_elem_1: "lift x {z} = {x \<union> lift x z}"
  by (auto simp:lift_elem_add  add_eq_union_lift)

lemma lift_elem_2: "lift x (y \<union> {z}) = lift x y \<union> {x \<union> lift x z}"
  unfolding lift_bin_union_distrib by (simp add: lift_elem_1)

lemma adduct_distrib: "x + (adduct y z) = adduct (x + y) (x + z)"
  unfolding adduct_def add_eq_union_lift by (auto simp: lift_elem_2)

text\<open>Proposition 3.3\<close>
lemma add_zero_left: "{} + X = X"
proof (induct X rule: mem_induction)
  case (1 X)
  have "{} + X = lift {} X" by (simp add: add_eq_union_lift)
  also have "... = X" by (simp add: lift_eq_image_add 1)
  finally show ?case .
qed

theorem assoc_add: "(X + Y) + Z = X + (Y + Z)"
proof(induct Z rule: mem_induction)
  case (1 Z)
  have"(X + Y) + Z = (X + Y) \<union> (lift (X + Y) Z)"
    by (simp add: add_eq_union_lift)
  also have"... = (X + Y) \<union> {(X + Y) + z | z \<in> Z }"
    by (simp add: lift_eq_image_add)
  also have"... = X \<union> (lift X Y) \<union> {(X + Y) + z | z \<in> Z }"
    by (simp add:add_eq_union_lift)
  also have"... = X \<union> (lift X Y) \<union> { X + (Y + z) | z \<in> Z }"
    by (simp add:1)
  also have"... = X \<union> lift X (Y + Z)"
  proof-
    have "lift X (Y + Z) = lift X (Y \<union> lift Y Z)"
      by (simp add: add_eq_union_lift)
    also have "... = (lift X Y) \<union> lift X (lift Y Z)"
      by (simp add:lift_bin_union_distrib)
    also have "... = (lift X Y) \<union> { X + (Y + z) | z \<in> Z }"
      by (simp add:lift_eq_image_add)
    also have "lift X (Y + Z) = (lift X Y) \<union> { X + (Y + z) | z \<in> Z }"
      sorry 
        (*do not know why it can not prove directly*)
    then show ?thesis by auto
  qed
    also have "... = X + (Y + Z)" 
      by (simp add: add_eq_union_lift)
    finally show ?case .
qed

definition "TC \<equiv> transrec (\<lambda>f x. x \<union> \<Union>(image f x)) "

lemma TC_image: "TC X = X \<union> \<Union>{TC u | u\<in>X}"
  by (auto simp:TC_def transrec_eq)

definition "Less X Y \<equiv> X \<in> TC Y"

lemma less_eq_TC: "Less X Y = (X \<in> TC Y)"
  by (simp add: Less_def)

(*this is an important implication*)
(*if A \<Longrightarrow> B, I want A, but I can prove B*)
lemma less_not_in: "Less X Y \<Longrightarrow> \<not> (X \<subseteq> Y)"
  sorry

lemma add_sub_in_add: 
  assumes "y \<in> z" 
  shows "(x + y) \<in> (x + z)"
proof-
  have "x + z = x \<union> lift x z " by (simp add:add_eq_union_lift)
  also have "lift x z = image ((+)x) z " 
    by (auto simp:lift_eq_image_add)
  also have "... = {x + zz| zz \<in> z}" by simp
  also have "y \<in> z \<Longrightarrow> x + y \<in> {x + zz| zz \<in> z}" by auto
  then show ?thesis sorry
qed

lemma less_sub_less: "y \<in> Y \<Longrightarrow> ( Y \<subseteq> X \<Longrightarrow> y \<subseteq> X) "
  sorry

lemma less_sub_less_conposi: "y \<in> Y \<Longrightarrow> (\<not>(y \<subseteq> X) \<Longrightarrow> \<not>(Y \<subseteq> X)) "
  sorry

lemma add_more_not_less: "\<not>((X + Y) \<subseteq> X) "
proof (induction Y rule:mem_induction)
  case (1 Y)
  have "\<And>y. y \<in> Y \<Longrightarrow> \<not> X + y \<subseteq> X" by (simp add:1)
  also have "\<And>y. y \<in> Y \<Longrightarrow> X + y \<in> X + Y"
    by (simp add: add_sub_in_add)
  then show ?case sorry
(*contradiction needed*)
qed

definition "mul X \<equiv> transrec (\<lambda>mulX Y. \<Union>(image (\<lambda>u. lift (mulX u) X) Y))"

bundle hotg_mul_syntax begin notation mul (infixl "*" 70) end
bundle no_hotg_mul_syntax begin no_notation add (infixl "*" 70) end
unbundle hotg_mul_syntax

lemma mul_eq_union_lift_mul: "x * y = \<Union>{lift (x * u) x | u \<in> y}"
  by (auto simp:mul_def transrec_eq)

lemma elts_multE:
  assumes "mem z (x * y)" 
  obtains u v where "mem u x" "mem v y" "z = x * v + u" 
  sorry

(*
lemma mul_eq_mul_add: "x * y = {x * u + r | (u \<in> y) \<and> r \<in> x }"
*)

lemma mul_zero: "x * {} = {}"
  sorry
(*
by (auto simp:  Union_Intersection.union_empty_eq  )
*)


end
