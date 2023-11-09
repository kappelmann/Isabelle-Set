theory Arithmetics
  imports
    Functions_Restrict
    Mem_Trans
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

(*TODO Kevin: rename to binary_relation_restrict*)
unbundle no_restrict_syntax

unbundle no_HOL_groups_syntax

abbreviation "zero_set \<equiv> {}"
abbreviation "one_set \<equiv> {zero_set}"

bundle hotg_set_zero_syntax begin notation zero_set ("0") end
bundle no_hotg_set_zero_syntax begin no_notation zero_set ("0") end

bundle hotg_set_one_syntax begin notation one_set ("1") end
bundle no_hotg_set_one_syntax begin no_notation one_set ("1") end

unbundle
  hotg_set_zero_syntax
  hotg_set_one_syntax


overloading
  fun_restrict_set \<equiv> "fun_restrict :: (set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> 'a"
begin
  definition "fun_restrict_set f X x \<equiv> if x \<in> X then f x else undefined"
end

lemma fun_restrict_set_eq_fun_restrict [simp]: "(f :: set \<Rightarrow> 'a)\<restriction>\<^bsub>X\<^esub> = f\<restriction>\<^bsub>mem_of X\<^esub>"
  unfolding fun_restrict_set_def by auto

axiomatization transrec :: "((set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a"
  where transrec_eq: "transrec f X = f ((transrec f)\<restriction>\<^bsub>X\<^esub>) X"

definition "image f A \<equiv> {f x | x \<in> A}"

lemma image_eq_repl [simp]: "image f A = {f x | x \<in> A}"
  unfolding image_def by simp

lemma repl_fun_restrict_mem_of_eq_repl [simp]: "{f\<restriction>\<^bsub>A\<^esub> x | x \<in> A} = {f x | x \<in> A}"
  by simp

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

lemma add_one_eq_adduct_self: "x + 1 = adduct x x"
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

definition "mem_trans_closure \<equiv> transrec (\<lambda>f x. x \<union> \<Union>(image f x))" 

lemma mem_trans_closure_eq_bin_union_repl:
  "mem_trans_closure X = X \<union> \<Union>{mem_trans_closure x | x \<in> X}"
  by (simp add: mem_trans_closure_def transrec_eq[where ?X=X])

lemma mem_trans_closure_empty_eq_empty [simp]: "mem_trans_closure {} = {}"
  by (simp add: mem_trans_closure_eq_bin_union_repl[where ?X="{}"])

(*TODO Kevin: rename mem_trans to mem_trans_closed*)
lemma mem_trans_mem_trans_closure: "mem_trans (mem_trans_closure X)"
  apply (rule mem_transI')
  apply (simp add: mem_trans_closure_eq_bin_union_repl[where ?X=X])
  sorry

lemma add_mem_add_if_mem:
  assumes "y \<in> z"
  shows "x + y \<in> x + z"
proof-
  have "lift x z = image ((+)x) z "
    by (auto simp:lift_eq_image_add)
  also have "... = {x + zz| zz \<in> z}" by simp
  finally have lift_image:"lift x z =  {x + zz| zz \<in> z}" .
  have add_lift:"x + z = x \<union> lift x z " 
    by (simp add: add_eq_bin_union_lift)
  then have add_image:"x + z = x \<union> {x + zz| zz \<in> z}"
    by (auto simp: lift_image)
  also have "{x + zz| zz \<in> z} \<subseteq> x \<union> {x + zz| zz \<in> z}" by auto
  then have "{x + zz| zz \<in> z} \<subseteq> x + z" 
    by (simp add: add_image)
  have "y \<in> z \<Longrightarrow> x + y \<in> {x + zz| zz \<in> z}" by auto
  then have "x + y \<in> x + z" 
    by (auto simp: add_image assms)
  then show ?thesis .
qed

definition "lt X Y \<equiv> X \<in> mem_trans_closure Y"

bundle hotg_lt_syntax begin notation lt (infix "<" 60) end
bundle no_hotg_lt_syntax begin no_notation lt (infix "<" 60) end
unbundle hotg_lt_syntax

lemma lt_iff_mem_trans_closure: "X < Y \<longleftrightarrow> X \<in> mem_trans_closure Y"
  unfolding lt_def by simp

(*
lemma not_subset_if_lt: "X < Y \<Longrightarrow> \<not>(Y \<subseteq> X)"
  sorry
*)

lemma lt_if_lt_if_mem: 
  assumes "y \<in> Y" "Y < X"
  shows "y < X"
  using assms unfolding lt_iff_mem_trans_closure
  using mem_trans_mem_trans_closure by auto

lemma not_lt_self [iff]: "\<not>(X < X)"
  apply (rule notI)
  apply (subst (asm) lt_iff_mem_trans_closure)
  sorry (*look at Foundation.thy*)

lemma add_more_not_less: "\<not>(X + Y < X)"
proof (rule notI)
  assume "X + Y < X"
  then show False
  proof (induction Y arbitrary: X rule: mem_induction)
    case (mem Y)
    (* moreover have "\<And>y. y \<in> Y \<Longrightarrow> X + y \<in> X + Y" 
      by (simp add: add_mem_add_if_mem) *)
    then show ?case
    proof (cases "Y = {}")
      case False
      then obtain y where "y \<in> Y" by blast
      with add_mem_add_if_mem have "X + y \<in> X + Y" by simp
      then have "X + y < X"
        using lt_if_lt_if_mem add_mem_add_if_mem sorry
      then show ?thesis sorry
    qed simp
  qed
qed

lemma trans_closure_inter_lift_eq_zero :"mem_trans_closure x \<inter> lift x y = {}"
  sorry

lemma assoc_lift: "lift X (lift Y Z) = lift (X + Y) Z" 
proof-
  have "lift X (lift Y Z) = {X + (Y + z) | z \<in> Z}"
    by (simp add: lift_eq_image_add)
  also have "... =  {(X + Y) + z | z \<in> Z}"
    by (simp add: assoc_add)
  also have "... = lift (X + Y) Z"
    by (simp add:lift_eq_image_add)
  finally have "lift X (lift Y Z) = lift (X + Y) Z" .
  then show ?thesis by simp
qed

find_theorems (100) name:"antis"
paragraph\<open>Proposition 3.4\<close>

lemma elim_union: "A \<union> B = A \<union> C \<Longrightarrow> B = C"
proof(induction A rule: mem_induction)
  case (mem A)
  then show ?case sorry
qed


(*
Subset.subsetI: (\<And>x. x \<in> ?A \<Longrightarrow> x \<in> ?B) \<Longrightarrow> ?A \<subseteq> ?B
Basic.eq_if_subset_if_subset: ?X \<subseteq> ?Y \<Longrightarrow> ?Y \<subseteq> ?X \<Longrightarrow> ?X = ?Y
*)
lemma lift_eq_iff_eq: "lift X Y = lift X Z \<longleftrightarrow> Y = Z"
proof (rule iffI)
  assume "lift X Y = lift X Z"
  then show "Y = Z"
  proof(induction Y arbitrary: Z rule: mem_induction)
    case (mem Y) show ?case
    proof (rule eq_if_subset_if_subset)
      show "Y \<subseteq> Z" sorry
      show "Z \<subseteq> Y" sorry
    qed
  qed
next
  assume "Y = Z"
  thus "lift X Y = lift X Z" by auto
qed

lemma add_eq_iff_eq: "X + Y = X + Z \<longleftrightarrow> Y = Z"
proof (rule iffI)
  assume left:"X + Y = X + Z"
  thus "Y = Z"
  proof-
    have "X + Y = X \<union> lift X Y" " X + Z = X \<union> lift X Z"
      by (auto simp: add_eq_bin_union_lift)
    then have "X \<union> lift X Y  = X \<union> lift X Z"
      by (simp add: left)
    then have "lift X Y = lift X Z" by (simp add: elim_union)
    then have "Y = Z" by (simp add:lift_eq_iff_eq)
    then show ?thesis .
  qed
next
  assume "Y = Z"
  thus "X + Y = X + Z"
    by auto
qed

(*TODO*)
lemma add_mem_add_iif_mem: "X + Y \<in> X + Z \<longleftrightarrow> Y \<in> Z"
proof (rule iffI)
  assume left:"X + Y \<in> X + Z"
  thus "Y \<in> Z"
  proof-
    have "X + Y \<in> X + Z"  by (simp add:left)
    also have "... = X \<union> lift X Z"
      by (auto simp: add_eq_bin_union_lift)
    finally have "X + Y \<in> X \<union> lift X Z" .
    have  add_more_not_less: "\<not> X + Y < X"
      by (auto simp: add_more_not_less)
    then have "X + Y \<in> lift X Z" sorry 
    then show ?thesis sorry
  qed
next
  assume "Y \<in> Z"
  thus "X + Y \<in> X + Z"
    by (simp add: add_mem_add_if_mem)
qed

paragraph\<open>Multiplication\<close>

definition "mul X \<equiv> transrec (\<lambda>mulX Y. \<Union>(image (\<lambda>y. lift (mulX y) X) Y))"

bundle hotg_mul_syntax begin notation mul (infixl "*" 70) end
bundle no_hotg_mul_syntax begin no_notation mul (infixl "*" 70) end
unbundle hotg_mul_syntax

(*can not use*)
lemma mul_eq_union_repl_lift_mul: "X * Y = \<Union>{lift (X * y) X | y \<in> Y}"
  by (auto simp:mul_def transrec_eq)

lemma elts_multE:
  assumes "z \<in> (X * Y)"
  obtains u v where "u \<in> x" "v \<in> y" "z = x * v + u"
  sorry

lemma mul_zero_eq_zero: "x * {} = {}"
  unfolding mul_def by (auto simp: transrec_eq)

lemma mul_one_same: "x * {{}} = x"
  unfolding mul_def by (auto simp: transrec_eq)

lemma mul_set_one_eq_lift: "X * {1} = lift X X"
proof-
  have 1:"\<And>Y.  X * Y = \<Union>{lift (X * y) X | y \<in> Y }" 
    by (simp add:mul_def transrec_eq)
  have "X * {1} = \<Union>{lift (X * y) X | y \<in> {1}}"
    by (simp add: mul_eq_union_repl_lift_mul[where ?Y="{1}"])
  also have "... = \<Union>{lift (X * {{}}) X }" by auto
  also have "... = \<Union>{lift X X}"
    by (simp add: mul_one_same)
  also have "... = lift X X" by auto
  finally have "X * {{{}}} = lift X X" .
    then show ?thesis by simp
  qed


(*Union to union lemma is needed*)
lemma mul_two_eq_add: "X * {{{}}, {}} = X + X"
proof-
  have 1:"X * Y = \<Union>{lift (X * y) X | y \<in> Y }" 
    by (simp add:mul_def transrec_eq)
  have "X * {{{}}, {}} = \<Union>{lift (X * y) X | y \<in> {{{}}, {}} }" 
    by (simp add: mul_eq_union_repl_lift_mul[where ?Y="{1,0}"])
  also have "... = (lift (X*{{}}) X) \<union> (lift (X*{}) X)" by auto
  also have "... = lift X X \<union> lift {} X" by (simp add: mul_one_same mul_zero_eq_zero)
  also have "... = X \<union> lift X X" by auto
  also have "... = X + X" by (simp add: add_eq_bin_union_lift)
  finally show ?thesis .
qed

end
