theory Arithmetics
  imports
    Functions_Restrict
    Union_Intersection
    Transport.HOL_Syntax_Bundles_Groups
    Transport.HOL_Syntax_Bundles_Orders
begin

paragraph \<open>Summary\<close>
text \<open>Translation of generalised arithmetics from
\<^url>\<open>https://www.isa-afp.org/entries/ZFC_in_HOL.html\<close>.\<close>

unbundle no_HOL_ascii_syntax
unbundle no_HOL_groups_syntax
unbundle no_HOL_order_syntax

definition "image f A \<equiv> {f x | x \<in> A}"

lemma image_eq_repl [simp]: "image f A = {f x | x \<in> A}"
  unfolding image_def by simp

axiomatization transrec :: "((set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a"
  where transrec_eq: "transrec f X = f (fun_restrict (transrec f) (mem_of X)) X"

paragraph\<open>Addition\<close>

definition "add X \<equiv> transrec (\<lambda>addX Y. X \<union> image addX Y)"

bundle hotg_add_syntax begin notation add (infixl "+" 65) end
bundle no_hotg_add_syntax begin no_notation add (infixl "+" 65) end
unbundle hotg_add_syntax

lemma add_eq_bin_union_image_add: "X + Y = X \<union> image ((+) X) Y"
  unfolding add_def by (simp add: transrec_eq)

definition "lift X \<equiv> image ((+) X)"

lemma lift_eq_image_add: "lift X = image ((+) X)"
  unfolding lift_def by simp

lemma add_eq_bin_union_lift: "X + Y = X \<union> lift X Y"
  unfolding lift_eq_image_add by (subst add_eq_bin_union_image_add) simp

lemma lift_bin_union_eq_lift_bin_union_lift: "lift X (A \<union> B) = lift X A \<union> lift X B"
  by (auto simp: lift_eq_image_add)

lemma lift_union_eq_union_image_lift: "lift X (\<Union>Y) = \<Union>(image (lift X) Y)"
  by (auto simp: lift_eq_image_add)

lemma idx_union_add_eq_add_idx_union:
  "Y \<noteq> {} \<Longrightarrow> (\<Union>y \<in> Y. X + f y) = X + (\<Union>y \<in> Y. f y)"
  by (simp add: lift_union_eq_union_image_lift add_eq_bin_union_lift)

lemma lift_zero_eq_zero [simp]: "lift X {} = {}"
  by (auto simp: lift_eq_image_add)

lemma add_zero_eq_self [simp]: "x + {} = x"
  unfolding add_eq_bin_union_lift by simp

lemma lift_one_eq_single_self [simp]: "lift x {{}} = {x}"
  unfolding lift_def by simp

definition "adduct x y \<equiv> x \<union> {y}"

lemma adduct_eq: "adduct x y = x \<union> {y}"
  by (simp add: adduct_def)

lemma add_one_eq_adduct_self: "x + {{}} = adduct x x"
  by (simp add: add_eq_bin_union_lift adduct_eq)

lemma lift_single_eq_single_add: "lift x {z} = {x + z}"
  unfolding lift_def by simp

lemma lift_single_eq_single_bin_union_lift: "lift x {z} = {x \<union> lift x z}"
  by (simp only: lift_single_eq_single_add add_eq_bin_union_lift)

lemma lift_bin_union_single_eq_lift_bin_union:
  "lift x (y \<union> {z}) = lift x y \<union> {x \<union> lift x z}"
  by (simp only: lift_single_eq_single_bin_union_lift lift_bin_union_eq_lift_bin_union_lift)

lemma add_adduct_eq_adduct_add: "x + (adduct y z) = adduct (x + y) (x + z)"
  by (auto simp: adduct_eq lift_bin_union_single_eq_lift_bin_union add_eq_bin_union_lift)

paragraph\<open>Proposition 3.3\<close>

lemma zero_add_eq_self [simp]: "{} + X = X"
proof (induct X rule: mem_induction)
  case (mem X)
  have "{} + X = lift {} X" by (simp add: add_eq_bin_union_lift)
  also from mem have "... = X" by (simp add: lift_eq_image_add)
  finally show ?case .
qed

corollary lift_zero_eq_self [simp]: "lift {} X = X"
  by (simp add: lift_eq_image_add)

theorem assoc_add: "(X + Y) + Z = X + (Y + Z)"
proof(induct Z rule: mem_induction)
  case (mem Z)
  from add_eq_bin_union_lift have "(X + Y) + Z = (X + Y) \<union> (lift (X + Y) Z)" by simp
  also from lift_eq_image_add have "... = (X + Y) \<union> {(X + Y) + z | z \<in> Z}" by simp
  also from add_eq_bin_union_lift have "... = X \<union> (lift X Y) \<union> {(X + Y) + z | z \<in> Z}" by simp
  also from mem have "... = X \<union> (lift X Y) \<union> {X + (Y + z) | z \<in> Z}" by simp
  also have "... = X \<union> lift X (Y + Z)"
  proof-
    have "lift X (Y + Z) = lift X (Y \<union> lift Y Z)"
      by (simp add: add_eq_bin_union_lift)
    also have "... = (lift X Y) \<union> lift X (lift Y Z)"
      by (simp add: lift_bin_union_eq_lift_bin_union_lift)
    also have "... = (lift X Y) \<union> {X + (Y + z) | z \<in> Z}"
      by (simp add: lift_eq_image_add)
    finally have "lift X (Y + Z) = (lift X Y) \<union> {X + (Y + z) | z \<in> Z}" .
    then show ?thesis by auto
  qed
    also from add_eq_bin_union_lift have "... = X + (Y + Z)" by simp
    finally show ?case .
qed

definition "trans_closure \<equiv> transrec (\<lambda>f x. x \<union> \<Union>(image f x)) "

lemma trans_closure_eq_bin_union_repl:
  "trans_closure X = X \<union> \<Union>{trans_closure u | u \<in> X}"
  (*loops*)
  (* by (auto simp: trans_closure_def transrec_eq) *)
  oops

definition "lt X Y \<equiv> X \<in> trans_closure Y"

bundle hotg_lt_syntax begin notation lt (infix "<" 60) end
bundle no_hotg_lt_syntax begin no_notation lt (infix "<" 60) end
unbundle hotg_lt_syntax

lemma lt_iff_mem_trans_closure: "X < Y \<longleftrightarrow> X \<in> trans_closure Y"
  unfolding lt_def by simp

(*this is an important lemma*)
lemma not_subset_if_lt: "X < Y \<Longrightarrow> \<not>(Y \<subseteq> X)"
  sorry

lemma add_mem_add_if_mem:
  assumes "y \<in> z"
  shows "(x + y) \<in> (x + z)"
proof-
  have "x + z = x \<union> lift x z " by (simp add:add_eq_bin_union_lift)
  also have "lift x z = image ((+)x) z "
    by (auto simp:lift_eq_image_add)
  also have "... = {x + zz| zz \<in> z}" by simp
  also have "y \<in> z \<Longrightarrow> x + y \<in> {x + zz| zz \<in> z}" by auto
  then show ?thesis sorry
qed

lemma less_sub_less: "y \<in> Y \<Longrightarrow> (Y \<subseteq> X \<Longrightarrow> y \<subseteq> X) "
  sorry

lemma less_sub_less_conposi: "y \<in> Y \<Longrightarrow> (\<not>(y \<subseteq> X) \<Longrightarrow> \<not>(Y \<subseteq> X)) "
  sorry

lemma add_more_not_less: "\<not>((X + Y) \<subseteq> X) "
proof (induction Y rule: mem_induction)
  case (mem Y)
  have "\<And>y. y \<in> Y \<Longrightarrow> \<not>(X + y \<subseteq> X)" by (simp add: mem)
  moreover have "\<And>y. y \<in> Y \<Longrightarrow> X + y \<in> X + Y" by (simp add: add_mem_add_if_mem)
  ultimately show ?case sorry
(*contradiction needed*)
qed

paragraph\<open>Multiplication\<close>

definition "mul X \<equiv> transrec (\<lambda>mulX Y. \<Union>(image (\<lambda>y. lift (mulX y) X) Y))"

bundle hotg_mul_syntax begin notation mul (infixl "*" 70) end
bundle no_hotg_mul_syntax begin no_notation mul (infixl "*" 70) end
unbundle hotg_mul_syntax

lemma mul_eq_union_repl_lift_mul: "X * Y = \<Union>{lift (X * y) X | y \<in> Y}"
  by (auto simp:mul_def transrec_eq)

lemma elts_multE:
  assumes "mem z (X * Y)"
  obtains u v where "mem u x" "mem v y" "z = x * v + u"
  sorry

(*
lemma mul_eq_mul_add: "X * Y = {X * y + r | (u \<in> y) \<and> r \<in> x }"
*)

lemma mul_zero: "x * {} = {}"
  sorry
(*
by (auto simp:  Union_Intersection.union_empty_eq  )
*)


end
