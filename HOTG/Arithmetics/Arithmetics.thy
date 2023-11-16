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

lemma add_eq_zero_iff_and_eq_zero: "X + Y = 0 \<longleftrightarrow> X = 0 \<and> Y = 0"
proof safe
    assume add_zero:"X + Y = 0"
    show "X = 0" 
    proof-
      have "X + Y = X \<union> lift X Y" by(simp add:add_eq_bin_union_lift)
      then have "X \<union> lift X Y = 0" by (simp add:add_zero)
      then show ?thesis by simp
    qed 
  then show "Y = 0" if "X + Y = 0"
    using that by auto
qed auto

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

lemma subset_mem_trans_closure:"X \<subseteq> mem_trans_closure X"
  by (auto simp:mem_trans_closure_eq_bin_union_repl[where ?X= X])

lemma not_in_mem_trans_closure_not_in_set: 
 "\<not> (X \<in> mem_trans_closure Y) \<Longrightarrow> \<not> (X \<in>  Y)"
  by (auto simp:subset_mem_trans_closure not_mem_if_subset_if_not_mem)

lemma mem_trans_closure_empty_eq_empty [simp]: "mem_trans_closure {} = {}"
  by (simp add: mem_trans_closure_eq_bin_union_repl[where ?X="{}"])

(*TODO Kevin: rename mem_trans to mem_trans_closed*)
lemma mem_trans_mem_trans_closure: "mem_trans (mem_trans_closure X)"
proof (induction X rule: mem_induction)
  case (mem X)
  show ?case
  proof (rule mem_transI')
    fix x y assume "x \<in> mem_trans_closure X" "y \<in> x"
    then have "x \<in> X \<union> \<Union>{mem_trans_closure x | x \<in> X}" (is "_ \<in> _ \<union> ?tmem")
      by (simp flip: mem_trans_closure_eq_bin_union_repl)
    then consider (memX) "x \<in> X" | (memtmem) "x \<in> ?tmem" by blast
    then show "y \<in> mem_trans_closure X"
    proof cases
      case memX
      moreover have "y \<in> mem_trans_closure x" using \<open>y \<in> x\<close> subset_mem_trans_closure by blast
      ultimately show ?thesis by (subst mem_trans_closure_eq_bin_union_repl) blast
    next
      case memtmem
      then obtain z where "x \<in> mem_trans_closure z" "z \<in> X" by auto
      with \<open>y \<in> x\<close> mem have "y \<in> mem_trans_closure z" by auto
      with \<open>z \<in> X\<close> show ?thesis by (subst mem_trans_closure_eq_bin_union_repl) blast
    qed
  qed
qed

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

lemma lt_if_lt_if_mem: 
  assumes "y \<in> Y"
  shows "Y < X \<Longrightarrow> y < X"
  using assms unfolding lt_iff_mem_trans_closure
  using mem_trans_mem_trans_closure by auto

lemma not_lt_self [iff]: "\<not>(X < X)"
  apply (rule notI)
  apply (subst (asm) lt_iff_mem_trans_closure)
  sorry (*look at Foundation.thy*)

lemma add_more_not_less: "\<not>(X + Y < X)"
proof (induction Y arbitrary: X rule: mem_induction)
  case (mem Y)
  then show ?case
    proof (cases "Y = {}")
      case False
      then obtain y where sub:"y \<in> Y" by blast
      with add_mem_add_if_mem have sub_in:"X + y \<in> X + Y" by simp
      have IH:"\<not> (X + y < X)" by (auto simp: sub mem)
      then have "X + y \<in> X + Y \<Longrightarrow> X + Y < X \<Longrightarrow> X + y < X" 
        by (simp add: lt_if_lt_if_mem)
      then have " X + Y < X \<Longrightarrow> X + y < X"
        by (auto simp:sub_in)
      then have "\<not> (X + y < X) \<Longrightarrow> \<not> (X + Y < X)"
        by (auto simp: contrapos_np)
      then show ?thesis by (simp add: IH)
    qed simp
  qed

lemma add_more_not_in:"\<not> (X + Y \<in> X)"
proof -
  have "\<not> (X + Y < X)" by  (simp add:add_more_not_less)
  then show ?thesis     
    by (simp add: not_in_mem_trans_closure_not_in_set lt_iff_mem_trans_closure )
qed

lemma trans_closure_inter_lift_eq_empty :"mem_trans_closure X \<inter> lift X Y = {}"
proof-
  have "\<And>y. \<not>(X + y < X)" by (simp add:add_more_not_less)
  then have "\<And>y. X + y \<notin> mem_trans_closure X" by (simp add:lt_iff_mem_trans_closure)
  then have "{x|x\<in>mem_trans_closure X}  \<inter> {X + y| y\<in> Y} = {}"
    by auto
  then have "mem_trans_closure X \<inter> lift X Y = {}"
    by (auto simp: lift_eq_image_add)
  then show ?thesis by auto
qed

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

paragraph\<open>Proposition 3.4\<close>

(*
Subset.subsetI: (\<And>x. x \<in> ?A \<Longrightarrow> x \<in> ?B) \<Longrightarrow> ?A \<subseteq> ?B
Basic.eq_if_subset_if_subset: ?X \<subseteq> ?Y \<Longrightarrow> ?Y \<subseteq> ?X \<Longrightarrow> ?X = ?Y
*)
lemma self_inter_lift_eq_empty[simp]: "X \<inter> lift X Y = {}"
proof-
  have 1:"mem_trans_closure X \<inter> lift X Y = {}" 
    by (simp add:trans_closure_inter_lift_eq_empty) 
  then have "(X \<union> \<Union>{mem_trans_closure x | x \<in> X}) \<inter> lift X Y = {}" 
    by (auto simp:mem_trans_closure_eq_bin_union_repl[where ?X = X])
  then show ?thesis by auto
  qed

lemma disjoint_union_elim: assumes "A \<inter> B = {}" "A \<inter> C = {}" "A \<union> B = A \<union> C"
  shows "B = C"
  using assms by auto

lemma lift_elim: 
  assumes"X \<union> lift X Y = X \<union> lift X Z "
  shows" lift X Y = lift X Z"
  by (rule disjoint_union_elim[of X]) (simp_all add: assms)

lemma lift_eq_iff_eq: "lift X Y = lift X Z \<longleftrightarrow> Y = Z"
proof (rule iffI)
  assume 1:"lift X Y = lift X Z"
  then show "Y = Z"
  proof(induction Y arbitrary: Z rule: mem_induction)
    case (mem Y) show ?case
    proof (rule eqI)
        show "u \<in> Z" if "u \<in> Y" for u 
        proof -
          have "lift X Z = lift X Y"by (simp add:mem)
          also have "... = {X + y |y \<in> Y}"by (simp add: lift_eq_image_add)
          finally have lift_eq_image_different_var:"lift X Z = {X + y| y \<in> Y}".
          have "X + u \<in> {X + y| y \<in> Y}" sorry
          then have "X + u \<in> (lift X Z)" by (simp add: lift_eq_image_different_var)
          then obtain v where "v \<in> Z" "X + u = X + v"
            using lift_def by auto
          then have "X \<union> lift X u  = X \<union> lift X v" 
            by (simp add: add_eq_bin_union_lift)
          then have "lift X u = lift X v" sorry
          then have "u = v" sorry
          then show ?thesis
            using \<open>v \<in> Z\<close> by blast
        qed
      next
        show "u \<in> Y" if "u \<in> Z" for u 
        proof -
          have "X + u \<in> (lift X Y)" sorry
          then obtain v where "v \<in> Y" "X + u = X + v"
            using lift_def by auto
          then have "lift X u = lift X v" sorry
          then have "u = v"sorry
          then show ?thesis
            using \<open>v \<in> Y\<close> by blast
        qed
    qed
  qed
qed auto



lemma add_eq_iff_eq: "X + Y = X + Z \<longleftrightarrow> Y = Z"
proof (rule iffI)
  assume left:"X + Y = X + Z"
  thus "Y = Z"
  proof-
    have "X + Y = X \<union> lift X Y" " X + Z = X \<union> lift X Z"
      by (auto simp: add_eq_bin_union_lift)
    then have 1:"X \<union> lift X Y  = X \<union> lift X Z"
      by (simp add: left)
    then have "lift X Y = lift X Z" 
    proof-
      have 2:"X \<union> lift X Y  = X \<union> lift X Z"  by (simp add:1)
      also have "X \<inter> lift X Y = {}" "X \<inter> lift X Y = {}" 
        by (auto simp:self_inter_lift_eq_empty)
      then show ?thesis sorry
    qed
    then have "Y = Z" by (simp add:lift_eq_iff_eq)
    then show ?thesis .
  qed
next
  assume "Y = Z"
  thus "X + Y = X + Z"
    by auto
qed

lemma add_mem_add_iff_mem: "X + Y \<in> X + Z \<longleftrightarrow> Y \<in> Z"
proof (rule iffI)
  assume left:"X + Y \<in> X + Z"
  thus "Y \<in> Z"
  proof-
    have "X + Y \<in> X + Z"  by (simp add:left)
    also have "... = X \<union> lift X Z"
      by (auto simp: add_eq_bin_union_lift)
    finally have "X + Y \<in> X \<union> lift X Z" .
    have add_more_not_less: "\<not> X + Y \<in> X"
      by (auto simp: add_more_not_in)
    with \<open>X + Y \<in> X \<union> lift X Z\<close> have "X + Y \<in> lift X Z" by auto

(*X and lift X Y(Z) are disjoint *)
    then show ?thesis sorry
  qed
next
  assume "Y \<in> Z"
  thus "X + Y \<in> X + Z"
    by (simp add: add_mem_add_if_mem)
qed

lemma mem_plus_V_E:
  assumes l: "l \<in> elts (x + y)"
  obtains "l \<in> elts x" | z where "z \<in> elts y" "l = x + z"
  sorry

corollary add_less_cancel_left [iff]:
  "x + y \<subseteq> x + z \<longleftrightarrow> y \<subseteq> z"
  sorry


paragraph\<open>Multiplication\<close>

definition "mul X \<equiv> transrec (\<lambda>mulX Y. \<Union>(image (\<lambda>y. lift (mulX y) X) Y))"

bundle hotg_mul_syntax begin notation mul (infixl "*" 70) end
bundle no_hotg_mul_syntax begin no_notation mul (infixl "*" 70) end
unbundle hotg_mul_syntax

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

lemma mul_two_eq_add: "X * {{{}}, {}} = X + X"
proof-
  have "X * {{{}}, {}} = \<Union>{lift (X * y) X | y \<in> {{{}}, {}} }" 
    by (simp add: mul_eq_union_repl_lift_mul[where ?Y="{1,0}"])
  also have "... = (lift (X*{{}}) X) \<union> (lift (X*{}) X)" by auto
  also have "... = lift X X \<union> lift {} X" by (simp add: mul_one_same mul_zero_eq_zero)
  also have "... = X \<union> lift X X" by auto
  also have "... = X + X" by (simp add: add_eq_bin_union_lift)
  finally show ?thesis .
qed

end
